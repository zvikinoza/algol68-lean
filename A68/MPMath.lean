import A68.MP

/-!
# A68.MPMath — a68g's multi-precision elementary functions

Re-implementations of `mp-math.c` and `mp-pi.c` for the level-2 build:
Newton iterations seeded from `double` estimates (`sqrt`, `cbrt`, `log`, `atan`
of the C library), Taylor series with a68g's stopping rule, argument reductions
(halving for `exp`, thirds for `sin`), and a68g's caches.

The caches make results depend on history, exactly as in a68g: `mp_pi` keeps
π and seven derived constants computed at the precision of the request that
last needed more digits, and later requests for fewer digits *truncate* the
cached value; `mp_ln_scale` (ln 10⁷) and `mp_ln_10` are kept at full precision
and rounded on each use.  `Cache` is that state, threaded through `MM`.
-/
namespace A68.MP

structure PiConsts where
  pi : MP
  halfPi : MP
  sqrtPi : MP
  lnPi : MP
  twoPi : MP
  sqrtTwoPi : MP
  piOver180 : MP
  d180OverPi : MP
  deriving Inhabited

structure Cache where
  /-- `(mp_pi_size, constants)`. -/
  pi : Option (Nat × PiConsts) := none
  /-- `(mp_ln_scale_size, value)`. -/
  lnScale : Option (Nat × MP) := none
  /-- `(mp_ln_10_size, value)`. -/
  ln10 : Option (Nat × MP) := none
  deriving Inhabited

abbrev MM := StateT Cache MPE

inductive PiMod where
  | pi | halfPi | twoPi | sqrtTwoPi | sqrtPi | lnPi | d180OverPi | piOver180

@[inline] def lift (x : MPE α) : MM α := StateT.lift x

/-- `DOUBLE_ACCURACY`: `A68G_REAL_DIG - 1`. -/
def doubleAccuracy : Nat := 14

/-- `must_reduce_mp`: |z| > 0.001, as a68g estimates it. -/
def mustReduce (z : MP) (digs : Nat) : MPE Bool := do
  if z.isZero then return false
  let expo : Int := z.ex * logR
  if expo ≥ 0 then return true
  if expo < -2 * (logR : Int) then return false
  let mut est : Float := Float.ofInt (z.dig 1).natAbs * (← tenUpReal (expo * logR))
  if digs > 1 then
    est := est + (Float.ofInt (z.dig 2) * Float.ofInt expo) / (← tenUpReal logR)
  return est > 0.001

/-- `same_mp`. -/
def sameMp (x y : MP) (digs : Nat) : Bool := Id.run do
  if x.isNaN || y.isNaN then return false
  if x.st != y.st || x.ex != y.ex then return false
  for k in [1:digs+1] do
    if x.dig k != y.dig k then return false
  return true

/-- `SET_MP_ONE`. -/
def setOne (z : MP) (digs : Nat) : MP := setMp z 1 0 digs

mutual

/-- `sqrt_mp (z, x, digs)`. -/
partial def sqrtMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setNaN z
  if x.dig 1 == 0 then return setZero z digs
  if x.dig 1 < 0 then return setNaN z
  let gdigs := digs + guards
  let mut zg := nil gdigs
  let mut xg := lenMp x digs gdigs
  let mut tmp := nil gdigs
  let reciprocal := xg.ex < 0
  if reciprocal then xg ← recMp xg xg gdigs
  if xg.ex.natAbs ≥ 2 then
    let expo := xg.ex
    xg := { xg with ex := Int.tmod expo 2 }
    zg ← sqrtMp zg xg gdigs
    zg := { zg with ex := zg.ex + Int.tdiv expo 2 }
  else
    let xd ← mpToReal xg gdigs
    zg ← realToMp zg (Float.sqrt xd) gdigs
    let mut decimals := doubleAccuracy
    repeat
      decimals := decimals * 2
      let hdigs := min (1 + decimals / logR) gdigs
      tmp ← divMp tmp xg zg hdigs
      tmp ← addMp tmp zg tmp hdigs
      zg ← halfMp zg tmp hdigs
      if !(decimals < 2 * gdigs * logR) then break
  if reciprocal then zg ← recMp zg zg digs
  shortenMp z digs zg gdigs

end

/-- `curt_mp (z, x, digs)`. -/
partial def curtMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setNaN z
  if x.dig 1 == 0 then return setZero z digs
  let changeSign := x.dig 1 < 0
  let x := if changeSign then x.negate1 else x
  let gdigs := digs + guards
  let mut zg := nil gdigs
  let mut xg := lenMp x digs gdigs
  let mut tmp := nil gdigs
  let reciprocal := xg.ex < 0
  if reciprocal then xg ← recMp xg xg gdigs
  if xg.ex.natAbs ≥ 3 then
    let expo := xg.ex
    xg := { xg with ex := Int.tmod expo 3 }
    zg ← curtMp zg xg gdigs
    zg := { zg with ex := zg.ex + Int.tdiv expo 3 }
  else
    let xd ← mpToReal xg gdigs
    zg ← realToMp zg (Float.cbrt xd) gdigs
    let mut decimals := doubleAccuracy
    repeat
      decimals := decimals * 2
      let hdigs := min (1 + decimals / logR) gdigs
      tmp ← mulMp tmp zg zg hdigs
      tmp ← divMp tmp xg tmp hdigs
      tmp ← addMp tmp zg tmp hdigs
      tmp ← addMp tmp zg tmp hdigs
      zg ← divMpDigit zg tmp 3 hdigs
      if !(decimals < gdigs * logR) then break
  if reciprocal then zg ← recMp zg zg digs
  let r ← shortenMp z digs zg gdigs
  return if changeSign then r.negate1 else r

/-- The Taylor terms `x^k / k!` for `k = 2 … 9` that `exp_mp` and `expm1_mp` add
    without a test, followed by the open-ended loop. -/
def expSeries (sum0 xg : MP) (gdigs : Nat) : MPE MP := do
  let mut sum := sum0
  sum ← addMp sum sum xg gdigs
  let mut pwr ← mulMp (nil gdigs) xg xg gdigs
  let mut tmp ← halfMp (nil gdigs) pwr gdigs
  sum ← addMp sum sum tmp gdigs
  for f in [6, 24, 120, 720, 5040, 40320, 362880] do
    pwr ← mulMp pwr pwr xg gdigs
    tmp ← divMpDigit tmp pwr f gdigs
    sum ← addMp sum sum tmp gdigs
  pwr ← mulMp pwr pwr xg gdigs
  let mut fac := setMp (nil gdigs) 3628800 0 gdigs
  let mut n : Int := 10
  let mut iter := pwr.dig 1 != 0
  while iter do
    tmp ← divMp tmp pwr fac gdigs
    if tmp.ex ≤ sum.ex - gdigs then iter := false
    else
      sum ← addMp sum sum tmp gdigs
      pwr ← mulMp pwr pwr xg gdigs
      n := n + 1
      fac ← mulMpDigit fac fac n gdigs
  return sum

/-- `exp_mp (z, x, digs)`. -/
def expMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setZero z digs
  let gdigs := digs + guards
  if x.dig 1 == 0 then return setOne z digs
  let mut xg := lenMp x digs gdigs
  let mut m := 0
  while (← mustReduce xg gdigs) do
    m := m + 1
    xg ← halfMp xg xg gdigs
  let mut sum ← expSeries (setOne (nil gdigs) gdigs) xg gdigs
  for _ in [0:m] do sum ← mulMp sum sum sum gdigs
  shortenMp z digs sum gdigs

/-- `expm1_mp (z, x, digs)` (a68g returns 1 for a zero argument). -/
def expm1Mp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMp z (-1) 0 digs
  let gdigs := digs + guards
  if x.dig 1 == 0 then return setOne z digs
  let xg := lenMp x digs gdigs
  let sum ← expSeries (nil gdigs) xg gdigs
  shortenMp z digs sum gdigs

mutual

/-- `ln_mp`, `mp_ln_scale`, `mp_ln_10`. -/
partial def lnMp (z x : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x)
  if x.isPInf then return setPInf z
  if x.isMInf then return setNaN z
  if x.dig 1 == 0 then return setMInf z
  if x.dig 1 < 0 then return setNaN z
  let gdigs := digs + guards
  let mut expo : Int := 0
  let mut xg := lenMp x digs gdigs
  let mut zg := nil gdigs
  let neg := xg.ex < 0
  if neg then xg ← lift (recMp xg xg digs)
  let scale := xg.ex.natAbs ≥ 2
  if scale then
    expo := xg.ex
    xg := { xg with ex := 0 }
  if xg.ex == 0 && xg.dig 1 == 1 && xg.dig 2 == 0 then
    let mut tmp := nil gdigs
    xg ← lift (minusOneMp xg xg gdigs)
    let mut pwr ← lift (mulMp (nil gdigs) xg xg gdigs)
    zg := moveMp zg xg gdigs
    let mut n : Int := 2
    let mut iter := pwr.dig 1 != 0
    while iter do
      tmp ← lift (divMpDigit tmp pwr n gdigs)
      if tmp.ex ≤ zg.ex - gdigs then iter := false
      else
        if n % 2 == 0 then tmp := tmp.negate1
        zg ← lift (addMp zg zg tmp gdigs)
        pwr ← lift (mulMp pwr pwr xg gdigs)
        n := n + 1
  else
    let mut tmp := nil gdigs
    let xd ← lift (mpToReal xg gdigs)
    zg ← lift (realToMp zg (Float.log xd) gdigs)
    let mut decimals := doubleAccuracy
    repeat
      decimals := decimals * 2
      let hdigs := min (1 + decimals / logR) gdigs
      tmp ← lift (expMp tmp zg hdigs)
      tmp ← lift (divMp tmp xg tmp hdigs)
      zg ← lift (minusOneMp zg zg hdigs)
      zg ← lift (addMp zg zg tmp hdigs)
      if !(decimals < gdigs * logR) then break
  if scale then
    let lnBase ← lnScale (nil gdigs) gdigs
    let lnBase ← lift (mulMpDigit lnBase lnBase expo gdigs)
    zg ← lift (addMp zg zg lnBase gdigs)
  if neg then zg := zg.negate1
  lift (shortenMp z digs zg gdigs)

/-- `mp_ln_scale (z, digs)`: ln R, kept at the longest precision computed so far. -/
partial def lnScale (z : MP) (digs : Nat) : MM MP := do
  let gdigs := digs + guards
  let c ← get
  let zg ← match c.lnScale with
    | some (size, v) =>
      if gdigs ≤ size then pure (moveMp (nil gdigs) v gdigs)
      else computeLnConst 1 1 gdigs (fun s v => { s with lnScale := some (gdigs, v) })
    | none => computeLnConst 1 1 gdigs (fun s v => { s with lnScale := some (gdigs, v) })
  lift (shortenMp z digs zg gdigs)

/-- `mp_ln_10 (z, digs)`. -/
partial def ln10 (z : MP) (digs : Nat) : MM MP := do
  let gdigs := digs + guards
  let c ← get
  let zg ← match c.ln10 with
    | some (size, v) =>
      if gdigs ≤ size then pure (moveMp (nil gdigs) v gdigs)
      else computeLnConst 10 0 gdigs (fun s v => { s with ln10 := some (gdigs, v) })
    | none => computeLnConst 10 0 gdigs (fun s v => { s with ln10 := some (gdigs, v) })
  lift (shortenMp z digs zg gdigs)

partial def computeLnConst (u : Int) (e : Int) (gdigs : Nat) (store : Cache → MP → Cache) : MM MP := do
  let zg0 := setMp (nil gdigs) u e gdigs
  let zg ← lnMp zg0 zg0 gdigs
  modify fun s => store s zg
  return zg

end

/-- `log_mp (z, x, digs)`. -/
def logMp (z x : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x)
  if x.isPInf then return setPInf z
  if x.isMInf then return setNaN z
  if x.dig 1 == 0 then return setMInf z
  if x.dig 1 < 0 then return setNaN z
  let z ← lnMp z x digs
  if z.isNaN then return setNaN z
  let l10 ← ln10 (nil digs) digs
  lift (divMp z z l10 digs)

-- ## π

mutual

/-- `mp_pi (api, mod, digs)`. -/
partial def piMp (api : MP) (md : PiMod) (digs : Nat) : MM MP := do
  let gdigs := digs + guards
  let need := match (← get).pi with
    | some (size, _) => decide (gdigs > size)
    | none => true
  if need then
    modify fun s => { s with pi := none }
    let mut piG := nil gdigs
    let two := lit gdigs 2 0
    let mut xg := lit gdigs 2 0
    let mut yg := nil gdigs
    let mut ug := nil gdigs
    let mut vg := nil gdigs
    xg ← lift (sqrtMp xg xg gdigs)
    piG ← lift (addMp piG xg two gdigs)
    yg ← lift (sqrtMp yg xg gdigs)
    repeat
      ug ← lift (sqrtMp ug xg gdigs)
      vg ← lift (recMp vg ug gdigs)
      ug ← lift (addMp ug ug vg gdigs)
      xg ← lift (halfMp xg ug gdigs)
      ug ← lift (plusOneMp ug xg gdigs)
      vg ← lift (plusOneMp vg yg gdigs)
      ug ← lift (divMp ug ug vg gdigs)
      vg ← lift (mulMp vg piG ug gdigs)
      if sameMp vg piG gdigs then break
      piG := moveMp piG vg gdigs
      ug ← lift (sqrtMp ug xg gdigs)
      vg ← lift (recMp vg ug gdigs)
      ug ← lift (mulMp ug yg ug gdigs)
      ug ← lift (addMp ug ug vg gdigs)
      vg ← lift (plusOneMp vg yg gdigs)
      yg ← lift (divMp yg ug vg gdigs)
    let api' ← lift (shortenMp api digs piG gdigs)
    let pi := moveMp (nil digs) api' digs
    let halfPi ← lift (halfMp (nil digs) api' digs)
    let sqrtPi ← lift (sqrtMp (nil digs) api' digs)
    let lnPi ← lnMp (nil digs) api' digs
    let twoPi ← lift (mulMpDigit (nil digs) api' 2 digs)
    let sqrtTwoPi ← lift (sqrtMp (nil digs) twoPi digs)
    let piOver180 ← lift (divMpDigit (nil digs) api' 180 digs)
    let d180OverPi ← lift (recMp (nil digs) piOver180 digs)
    modify fun s => { s with pi := some (gdigs, { pi, halfPi, sqrtPi, lnPi, twoPi, sqrtTwoPi, piOver180, d180OverPi }) }
    return ← fetchPi api' md digs
  fetchPi api md digs

partial def fetchPi (api : MP) (md : PiMod) (digs : Nat) : MM MP := do
  match (← get).pi with
  | some (_, c) =>
    let v := match md with
      | .pi => c.pi | .halfPi => c.halfPi | .twoPi => c.twoPi | .sqrtTwoPi => c.sqrtTwoPi
      | .sqrtPi => c.sqrtPi | .lnPi => c.lnPi | .d180OverPi => c.d180OverPi | .piOver180 => c.piOver180
    return moveMp api v digs
  | none => return setNaN api

end

-- ## Hyperbolic functions

/-- `hyp_mp (sh, ch, z, digs)`: returns `(sinh, cosh)`. -/
def hypMp (sh ch z : MP) (digs : Nat) : MPE (MP × MP) := do
  let zg := moveMp (nil digs) z digs
  let mut xg ← expMp (nil digs) zg digs
  let mut yg ← recMp (nil digs) xg digs
  let ch ← addMp ch xg yg digs
  let mut zg := zg
  if (xg.dig 1 == 1 && xg.dig 2 == 0) || (yg.dig 1 == 1 && yg.dig 2 == 0) then
    xg ← expm1Mp xg zg digs
    zg := zg.negate1
    yg ← expm1Mp yg zg digs
  let sh ← subMp sh xg yg digs
  let sh ← halfMp sh sh digs
  let ch ← halfMp ch ch digs
  return (sh, ch)

def sinhMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  let gdigs := digs + guards
  let (s, _) ← hypMp (nil gdigs) (nil gdigs) (lenMp x digs gdigs) gdigs
  shortenMp z digs s gdigs

def coshMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  let gdigs := digs + guards
  let (_, c) ← hypMp (nil gdigs) (nil gdigs) (lenMp x digs gdigs) gdigs
  shortenMp z digs c gdigs

def tanhMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  let gdigs := digs + guards
  let (s, c) ← hypMp (nil gdigs) (nil gdigs) (lenMp x digs gdigs) gdigs
  let q ← divMp c s c gdigs
  shortenMp z digs q gdigs

def asinhMp (z x : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x)
  if x.isZero then return setZero z digs
  let gdigs := if x.ex ≥ -1 then digs + guards else 2 * (digs + guards)
  let xg := lenMp x digs gdigs
  let zg ← lift (mulMp (nil gdigs) xg xg gdigs)
  let yg ← lift (addMp (nil gdigs) zg (setOne (nil gdigs) gdigs) gdigs)
  let yg ← lift (sqrtMp yg yg gdigs)
  let yg ← lift (addMp yg yg xg gdigs)
  let zg ← lnMp zg yg gdigs
  if zg.isZero then return moveMp z x digs
  lift (shortenMp z digs zg gdigs)

def acoshMp (z x : MP) (digs : Nat) : MM MP := do
  let gdigs := if x.dig 1 == 1 && x.dig 2 == 0 then 2 * (digs + guards) else digs + guards
  let xg := lenMp x digs gdigs
  let zg ← lift (mulMp (nil gdigs) xg xg gdigs)
  let yg ← lift (subMp (nil gdigs) zg (setOne (nil gdigs) gdigs) gdigs)
  let yg ← lift (sqrtMp yg yg gdigs)
  let yg ← lift (addMp yg yg xg gdigs)
  let zg ← lnMp zg yg gdigs
  lift (shortenMp z digs zg gdigs)

def atanhMp (z x : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x)
  let gdigs := digs + guards
  let xg := lenMp x digs gdigs
  let yg := setOne (nil gdigs) gdigs
  let zg ← lift (addMp (nil gdigs) yg xg gdigs)
  let yg ← lift (subMp yg yg xg gdigs)
  let yg ← lift (divMp yg zg yg gdigs)
  let zg ← lnMp zg yg gdigs
  let zg ← lift (halfMp zg zg gdigs)
  lift (shortenMp z digs zg gdigs)

-- ## Circular functions

mutual

/-- `sin_mp (z, x, digs)`. -/
partial def sinMp (z x : MP) (digs : Nat) : MM MP := do
  if !x.isFinite then return setNaN z
  let gdigs := digs + guards
  let pi ← piMp (nil gdigs) .pi gdigs
  let tpi ← piMp (nil gdigs) .twoPi gdigs
  let hpi ← piMp (nil gdigs) .halfPi gdigs
  let mut xg := lenMp x digs gdigs
  xg ← lift (modMp xg xg tpi gdigs)
  let neg := xg.dig 1 < 0
  if neg then xg := xg.negate1
  let mut tmp ← lift (subMp (nil gdigs) xg pi gdigs)
  let flip := tmp.dig 1 > 0
  if flip then xg ← lift (subMp xg xg pi gdigs)
  tmp ← lift (subMp tmp xg hpi gdigs)
  if tmp.dig 1 > 0 then xg ← lift (subMp xg pi xg gdigs)
  let mut m := 0
  while (← lift (mustReduce xg gdigs)) do
    m := m + 1
    xg ← lift (divMpDigit xg xg 3 gdigs)
  let sqr ← lift (mulMp (nil gdigs) xg xg gdigs)
  let mut pwr ← lift (mulMp (nil gdigs) sqr xg gdigs)
  let mut zg := moveMp (nil gdigs) xg gdigs
  tmp ← lift (divMpDigit tmp pwr 6 gdigs)
  zg ← lift (subMp zg zg tmp gdigs)
  pwr ← lift (mulMp pwr pwr sqr gdigs)
  tmp ← lift (divMpDigit tmp pwr 120 gdigs)
  zg ← lift (addMp zg zg tmp gdigs)
  pwr ← lift (mulMp pwr pwr sqr gdigs)
  tmp ← lift (divMpDigit tmp pwr 5040 gdigs)
  zg ← lift (subMp zg zg tmp gdigs)
  pwr ← lift (mulMp pwr pwr sqr gdigs)
  let mut fac := setMp (nil gdigs) 362880 0 gdigs
  let mut n : Int := 9
  let mut even := true
  let mut iter := pwr.dig 1 != 0
  while iter do
    tmp ← lift (divMp tmp pwr fac gdigs)
    if tmp.ex ≤ zg.ex - gdigs then iter := false
    else
      if even then
        zg ← lift (addMp zg zg tmp gdigs)
        even := false
      else
        zg ← lift (subMp zg zg tmp gdigs)
        even := true
      pwr ← lift (mulMp pwr pwr sqr gdigs)
      n := n + 1
      fac ← lift (mulMpDigit fac fac n gdigs)
      n := n + 1
      fac ← lift (mulMpDigit fac fac n gdigs)
  fac := setMp fac 3 0 gdigs
  for _ in [0:m] do
    pwr ← lift (mulMp pwr zg zg gdigs)
    pwr ← lift (mulMpDigit pwr pwr 4 gdigs)
    pwr ← lift (subMp pwr fac pwr gdigs)
    zg ← lift (mulMp zg pwr zg gdigs)
  let r ← lift (shortenMp z digs zg gdigs)
  return if neg != flip then r.negate1 else r

/-- `atan_mp (z, x, digs)`. -/
partial def atanMp (z x : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x)
  if x.isPInf then return ← piMp z .halfPi digs
  if x.isMInf then return (← piMp z .halfPi digs).negate1
  if x.dig 1 == 0 then return setZero z digs
  let gdigs := digs + guards
  let mut xg := lenMp x digs gdigs
  let mut zg := nil gdigs
  let neg := xg.dig 1 < 0
  if neg then xg := xg.negate1
  let flip := ((xg.ex > 0) || (xg.ex == 0 && xg.dig 1 > 1)) && xg.dig 1 != 0
  if flip then xg ← lift (recMp xg xg gdigs)
  if xg.ex < -1 || (xg.ex == -1 && xg.dig 1 < R / 100) then
    let sqr ← lift (mulMp (nil gdigs) xg xg gdigs)
    let mut pwr ← lift (mulMp (nil gdigs) sqr xg gdigs)
    let mut tmp := nil gdigs
    zg := moveMp zg xg gdigs
    let mut n : Int := 3
    let mut even := false
    let mut iter := pwr.dig 1 != 0
    while iter do
      tmp ← lift (divMpDigit tmp pwr n gdigs)
      if tmp.ex ≤ zg.ex - gdigs then iter := false
      else
        if even then
          zg ← lift (addMp zg zg tmp gdigs)
          even := false
        else
          zg ← lift (subMp zg zg tmp gdigs)
          even := true
        pwr ← lift (mulMp pwr pwr sqr gdigs)
        n := n + 2
  else
    let mut sns := nil gdigs
    let mut cns := nil gdigs
    let mut tmp := nil gdigs
    let xd ← lift (mpToReal xg gdigs)
    zg ← lift (realToMp zg (Float.atan xd) gdigs)
    let mut decimals := doubleAccuracy
    repeat
      decimals := decimals * 2
      let hdigs := min (1 + decimals / logR) gdigs
      sns ← sinMp sns zg hdigs
      tmp ← lift (mulMp tmp sns sns hdigs)
      tmp ← lift (oneMinusMp tmp tmp hdigs)
      cns ← lift (sqrtMp cns tmp hdigs)
      tmp ← lift (mulMp tmp xg cns hdigs)
      tmp ← lift (subMp tmp sns tmp hdigs)
      tmp ← lift (mulMp tmp tmp cns hdigs)
      zg ← lift (subMp zg zg tmp hdigs)
      if !(decimals < gdigs * logR) then break
  if flip then
    let hpi ← piMp (nil gdigs) .halfPi gdigs
    zg ← lift (subMp zg hpi zg gdigs)
  let r ← lift (shortenMp z digs zg gdigs)
  return if neg then r.negate1 else r

end

/-- `cos_mp (z, x, digs)`: `sin (π/2 - (x mod 2π))`. -/
def cosMp (z x : MP) (digs : Nat) : MM MP := do
  if !x.isFinite then return setNaN z
  let gdigs := digs + guards
  let hpi ← piMp (nil gdigs) .halfPi gdigs
  let tpi ← piMp (nil gdigs) .twoPi gdigs
  let xg ← lift (modMp (lenMp x digs gdigs) (lenMp x digs gdigs) tpi gdigs)
  let xg ← lift (subMp xg hpi xg gdigs)
  let y ← lift (shortenMp (nil digs) digs xg gdigs)
  sinMp z y digs

/-- `tan_mp (z, x, digs)`: `sin x / sqrt (1 - sin² x)` with the sign from `x mod π`. -/
def tanMp (z x : MP) (digs : Nat) : MM MP := do
  if !x.isFinite then return setNaN z
  let gdigs := digs + guards
  let pi ← piMp (nil gdigs) .pi gdigs
  let hpi ← piMp (nil gdigs) .halfPi gdigs
  let xg ← lift (modMp (lenMp x digs gdigs) (lenMp x digs gdigs) pi gdigs)
  let neg ← if xg.dig 1 ≥ 0 then do
      let yg ← lift (subMp (nil gdigs) xg hpi gdigs)
      pure (decide (yg.dig 1 > 0))
    else do
      let yg ← lift (addMp (nil gdigs) xg hpi gdigs)
      pure (decide (yg.dig 1 < 0))
  let x' ← lift (shortenMp x digs xg gdigs)
  let sns ← sinMp (nil digs) x' digs
  let cns ← lift (mulMp (nil digs) sns sns digs)
  let cns ← lift (oneMinusMp cns cns digs)
  let cns ← lift (sqrtMp cns cns digs)
  let r ← lift (divMp z sns cns digs)
  if r.isNaN then return setNaN r
  return if neg then r.negate1 else r

/-- `cot_mp`: like `tan_mp`, dividing the other way. -/
def cotMp (z x : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x)
  let gdigs := digs + guards
  let pi ← piMp (nil gdigs) .pi gdigs
  let hpi ← piMp (nil gdigs) .halfPi gdigs
  let xg ← lift (modMp (lenMp x digs gdigs) (lenMp x digs gdigs) pi gdigs)
  let neg ← if xg.dig 1 ≥ 0 then do
      let yg ← lift (subMp (nil gdigs) xg hpi gdigs)
      pure (decide (yg.dig 1 > 0))
    else do
      let yg ← lift (addMp (nil gdigs) xg hpi gdigs)
      pure (decide (yg.dig 1 < 0))
  let x' ← lift (shortenMp x digs xg gdigs)
  let sns ← sinMp (nil digs) x' digs
  let cns ← lift (mulMp (nil digs) sns sns digs)
  let cns ← lift (oneMinusMp cns cns digs)
  let cns ← lift (sqrtMp cns cns digs)
  let r ← lift (divMp z cns sns digs)
  if r.isNaN then return setNaN r
  return if neg then r.negate1 else r

/-- `asin_mp (z, x, digs)`. -/
def asinMp (z x : MP) (digs : Nat) : MM MP := do
  if !x.isFinite then return setNaN z
  let gdigs := digs + guards
  let xg := lenMp x digs gdigs
  let zg ← lift (mulMp (nil gdigs) xg xg gdigs)
  let zg ← lift (oneMinusMp zg zg gdigs)
  let zg ← lift (sqrtMp zg zg digs)
  if zg.isNaN then return setNaN z
  if zg.dig 1 == 0 then
    let r ← piMp z .halfPi digs
    return if xg.dig 1 ≥ 0 then r else r.negate1
  let xg ← lift (divMp xg xg zg gdigs)
  if xg.isNaN then return setNaN z
  let y ← lift (shortenMp (nil digs) digs xg gdigs)
  atanMp z y digs

/-- `acos_mp (z, x, digs)`. -/
def acosMp (z x : MP) (digs : Nat) : MM MP := do
  if !x.isFinite then return setNaN z
  let gdigs := digs + guards
  let neg := x.dig 1 < 0
  if x.dig 1 == 0 then return ← piMp z .halfPi digs
  let xg := lenMp x digs gdigs
  let zg ← lift (mulMp (nil gdigs) xg xg gdigs)
  let zg ← lift (oneMinusMp zg zg gdigs)
  let zg ← lift (sqrtMp zg zg digs)
  if zg.isNaN then return setNaN z
  let xg ← lift (divMp xg zg xg gdigs)
  if xg.isNaN then return setNaN z
  let y ← lift (shortenMp (nil digs) digs xg gdigs)
  let r ← atanMp z y digs
  if neg then
    let p ← piMp y .pi digs
    return ← lift (addMp r r p digs)
  return r

/-- `atan2_mp (z, x, y, digs)`: `z` receives the angle of the point `(x, y)`. -/
def atan2Mp (z x y : MP) (digs : Nat) : MM MP := do
  if x.dig 1 == 0 && y.dig 1 == 0 then return setNaN z
  let flip := y.dig 1 < 0
  let ya := y.setDig 1 (y.dig 1).natAbs
  let r ← if x.isZero then piMp z .halfPi digs
    else do
      let flop := x.dig 1 ≤ 0
      let xa := x.setDig 1 (x.dig 1).natAbs
      let q ← lift (divMp z ya xa digs)
      let q ← atanMp q q digs
      if flop then
        let t ← piMp (nil digs) .pi digs
        lift (subMp q t q digs)
      else pure q
  return if flip then r.negate1 else r

/-- `pow_mp (z, x, y, digs)`: `exp (y · ln x)`. -/
def powMp (z x y : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x); lift (catchNaN y)
  let l ← lnMp z x digs
  if l.isNaN then throw "invalid argument"
  let p ← lift (mulMp l y l digs)
  lift (expMp p p digs)

/-- `hypot_mp (z, x, y, digs)`. -/
def hypotMp (z x y : MP) (digs : Nat) : MPE MP := do
  catchNaN x; catchNaN y
  let u := (moveMp (nil digs) x digs)
  let u := u.setDig 1 (u.dig 1).natAbs
  let v := (moveMp (nil digs) y digs)
  let v := v.setDig 1 (v.dig 1).natAbs
  if u.isZero then return moveMp z v digs
  if v.isZero then return moveMp z u digs
  let t := setOne (nil digs) digs
  let d ← subMp z u v digs
  if d.dig 1 > 0 then
    let q ← divMp d v u digs
    let q ← mulMp q q q digs
    let q ← addMp q t q digs
    let q ← sqrtMp q q digs
    mulMp q u q digs
  else
    let q ← divMp d u v digs
    let q ← mulMp q q q digs
    let q ← addMp q t q digs
    let q ← sqrtMp q q digs
    mulMp q v q digs

-- ## LONG COMPLEX

/-- `cmul_mp (a, b, c, d, digs)`: `(a + bi)(c + di)` at two guard digits. -/
def cmulMp (a b c d : MP) (digs : Nat) : MPE (MP × MP) := do
  let gdigs := digs + guards
  let la := lenMp a digs gdigs
  let lb := lenMp b digs gdigs
  let lc := lenMp c digs gdigs
  let ld := lenMp d digs gdigs
  let ac ← mulMp (nil gdigs) la lc gdigs
  let bd ← mulMp (nil gdigs) lb ld gdigs
  let ad ← mulMp (nil gdigs) la ld gdigs
  let bc ← mulMp (nil gdigs) lb lc gdigs
  let la ← subMp la ac bd gdigs
  let lb ← addMp lb ad bc gdigs
  return (← shortenMp a digs la gdigs, ← shortenMp b digs lb gdigs)

/-- `cdiv_mp (a, b, c, d, digs)`: `(a + bi) / (c + di)` by the method that avoids
    overflow, dividing by the larger of `|c|` and `|d|`. -/
def cdivMp (a b c d : MP) (digs : Nat) : MPE (MP × MP) := do
  if c.dig 1 == 0 && d.dig 1 == 0 then return (setNaN a, setNaN b)
  let q := moveMp (nil digs) c digs
  let r := moveMp (nil digs) d digs
  let q := q.setDig 1 (q.dig 1).natAbs
  let r := r.setDig 1 (r.dig 1).natAbs
  let q ← subMp q q r digs
  if q.dig 1 ≥ 0 then
    let q ← divMp q d c digs
    if q.isNaN then return (setNaN a, setNaN b)
    let r ← mulMp r d q digs
    let r ← addMp r r c digs
    let c1 ← mulMp c b q digs
    let c1 ← addMp c1 c1 a digs
    let c1 ← divMp c1 c1 r digs
    let d1 ← mulMp d a q digs
    let d1 ← subMp d1 b d1 digs
    let d1 ← divMp d1 d1 r digs
    return (moveMp a c1 digs, moveMp b d1 digs)
  else
    let q ← divMp q c d digs
    if q.isNaN then return (setNaN a, setNaN b)
    let r ← mulMp r c q digs
    let r ← addMp r r d digs
    let c1 ← mulMp c a q digs
    let c1 ← addMp c1 c1 b digs
    let c1 ← divMp c1 c1 r digs
    let d1 ← mulMp d b q digs
    let d1 ← subMp d1 d1 a digs
    let d1 ← divMp d1 d1 r digs
    return (moveMp a c1 digs, moveMp b d1 digs)

-- ## LONG COMPLEX functions (`mp-complex.c`)

/-- `SET_MP_MINUS_ONE`. -/
def setMinusOne (z : MP) (digs : Nat) : MP := setMp z (-1) 0 digs

/-- `csqrt_mp (r, i, digs)`. -/
def csqrtMp (r i : MP) (digs : Nat) : MPE (MP × MP) := do
  let gdigs := digs + guards
  let mut re := lenMp r digs gdigs
  let mut im := lenMp i digs gdigs
  if re.isZero && im.isZero then
    re := setZero re gdigs
    im := setZero im gdigs
  else
    let c1 := lit gdigs 1 0
    let x := moveMp (nil gdigs) re gdigs
    let x := x.setDig 1 (x.dig 1).natAbs
    let y := moveMp (nil gdigs) im gdigs
    let y := y.setDig 1 (y.dig 1).natAbs
    let mut w ← subMp (nil gdigs) x y gdigs
    let mut u := nil gdigs
    let mut v := nil gdigs
    if w.dig 1 ≥ 0 then
      let t ← divMp (nil gdigs) y x gdigs
      v ← mulMp v t t gdigs
      u ← addMp u c1 v gdigs
      v ← sqrtMp v u gdigs
      u ← addMp u c1 v gdigs
      v ← halfMp v u gdigs
      u ← sqrtMp u v gdigs
      v ← sqrtMp v x gdigs
      w ← mulMp w u v gdigs
    else
      let t ← divMp (nil gdigs) x y gdigs
      v ← mulMp v t t gdigs
      u ← addMp u c1 v gdigs
      v ← sqrtMp v u gdigs
      u ← addMp u t v gdigs
      v ← halfMp v u gdigs
      u ← sqrtMp u v gdigs
      v ← sqrtMp v y gdigs
      w ← mulMp w u v gdigs
    if re.dig 1 ≥ 0 then
      re := moveMp re w gdigs
      u ← addMp u w w gdigs
      im ← divMp im im u gdigs
    else
      if im.dig 1 < 0 then w := w.negate1
      v ← addMp v w w gdigs
      re ← divMp re im v gdigs
      im := moveMp im w gdigs
  return (← shortenMp r digs re gdigs, ← shortenMp i digs im gdigs)

/-- `cexp_mp (r, i, digs)`. -/
def cexpMp (r i : MP) (digs : Nat) : MM (MP × MP) := do
  let gdigs := digs + guards
  let mut re := lenMp r digs gdigs
  let mut im := lenMp i digs gdigs
  if im.isZero then
    re ← lift (expMp re re gdigs)
  else
    let u ← lift (expMp (nil gdigs) re gdigs)
    re ← cosMp re im gdigs
    im ← sinMp im im gdigs
    re ← lift (mulMp re re u gdigs)
    im ← lift (mulMp im im u gdigs)
  return (← lift (shortenMp r digs re gdigs), ← lift (shortenMp i digs im gdigs))

/-- `cln_mp (r, i, digs)`. -/
def clnMp (r i : MP) (digs : Nat) : MM (MP × MP) := do
  let gdigs := digs + guards
  let re := lenMp r digs gdigs
  let im := lenMp i digs gdigs
  let s ← lift (hypotMp (nil gdigs) (moveMp (nil gdigs) re gdigs) (moveMp (nil gdigs) im gdigs) gdigs)
  let t ← atan2Mp (nil gdigs) (moveMp (nil gdigs) re gdigs) (moveMp (nil gdigs) im gdigs) gdigs
  let re ← lnMp re s gdigs
  let im := moveMp im t gdigs
  return (← lift (shortenMp r digs re gdigs), ← lift (shortenMp i digs im gdigs))

/-- `csin_mp`, and `ccos_mp` with `cosine := true`. -/
def csinCosMp (cosine : Bool) (r i : MP) (digs : Nat) : MM (MP × MP) := do
  let gdigs := digs + guards
  let mut re := lenMp r digs gdigs
  let mut im := lenMp i digs gdigs
  if im.isZero then
    re ← if cosine then cosMp re re gdigs else sinMp re re gdigs
    im := setZero im gdigs
  else
    let s ← sinMp (nil gdigs) re gdigs
    let c ← cosMp (nil gdigs) re gdigs
    let (sh, ch) ← lift (hypMp (nil gdigs) (nil gdigs) im gdigs)
    if cosine then
      re ← lift (mulMp re c ch gdigs)
      im ← lift (mulMp im s sh.negate1 gdigs)
    else
      re ← lift (mulMp re s ch gdigs)
      im ← lift (mulMp im c sh gdigs)
  return (← lift (shortenMp r digs re gdigs), ← lift (shortenMp i digs im gdigs))

/-- `ctan_mp (r, i, digs)`: `csin / ccos` at the same precision. -/
def ctanMp (r i : MP) (digs : Nat) : MM (MP × MP) := do
  let (su, sv) ← csinCosMp false (moveMp (nil digs) r digs) (moveMp (nil digs) i digs) digs
  let (cu, cv) ← csinCosMp true (moveMp (nil digs) r digs) (moveMp (nil digs) i digs) digs
  let (s, t) ← lift (cdivMp (moveMp (nil digs) su digs) (moveMp (nil digs) sv digs) cu cv digs)
  return (moveMp r s digs, moveMp i t digs)

/-- `casin_mp`, and `cacos_mp` with `arccos := true`. -/
def casinAcosMp (arccos : Bool) (r i : MP) (digs : Nat) : MM (MP × MP) := do
  let gdigs := digs + guards
  let re := lenMp r digs gdigs
  let im := lenMp i digs gdigs
  let negim := im.dig 1 < 0
  let c1 := lit gdigs 1 0
  let a ← lift (addMp (nil gdigs) re c1 gdigs)
  let b ← lift (subMp (nil gdigs) re c1 gdigs)
  let u ← lift (hypotMp (nil gdigs) a im gdigs)
  let v ← lift (hypotMp (nil gdigs) b im gdigs)
  let a ← lift (addMp a u v gdigs)
  let a ← lift (halfMp a a gdigs)
  let b ← lift (subMp b u v gdigs)
  let b ← lift (halfMp b b gdigs)
  let u ← lift (mulMp u a a gdigs)
  let u ← lift (subMp u u c1 gdigs)
  let u ← lift (sqrtMp u u gdigs)
  let u ← lift (addMp u a u gdigs)
  let im ← lnMp im u gdigs
  let re ← if arccos then acosMp re b gdigs else asinMp re b gdigs
  let flipIm := if arccos then !negim else negim
  let im := if flipIm then im.negate1 else im
  return (← lift (shortenMp r digs re gdigs), ← lift (shortenMp i digs im gdigs))

/-- `catan_mp (r, i, digs)`. -/
def catanMp (r i : MP) (digs : Nat) : MM (MP × MP) := do
  let gdigs := digs + guards
  let re := lenMp r digs gdigs
  let im := lenMp i digs gdigs
  let mut u := nil gdigs
  let mut v := nil gdigs
  if im.isZero then
    u ← atanMp u re gdigs
    v := setZero v gdigs
  else
    let c1 := lit gdigs 1 0
    let mut a ← lift (addMp (nil gdigs) im c1 gdigs)
    let mut b ← lift (subMp (nil gdigs) im c1 gdigs)
    u ← lift (hypotMp u re a gdigs)
    v ← lift (hypotMp v re b gdigs)
    u ← lift (divMp u u v gdigs)
    v ← lnMp v u gdigs
    v ← lift (halfMp v v gdigs)
    a ← lift (mulMp a re re gdigs)
    b ← lift (mulMp b im im gdigs)
    a ← lift (addMp a a b gdigs)
    u ← lift (subMp u c1 a gdigs)
    if u.isZero then
      u ← piMp u .halfPi gdigs
    else
      let neg := u.dig 1 < 0
      a ← lift (addMp a re re gdigs)
      a ← lift (divMp a a u gdigs)
      u ← atanMp u a gdigs
      if neg then
        a ← piMp a .pi gdigs
        u ← if re.dig 1 < 0 then lift (subMp u u a gdigs) else lift (addMp u u a gdigs)
      u ← lift (halfMp u u gdigs)
  return (← lift (shortenMp r digs u gdigs), ← lift (shortenMp i digs v gdigs))

/-- `csinh_mp`, `ccosh_mp`, `ctanh_mp`, `casinh_mp`, `cacosh_mp`, `catanh_mp`: the
    circular functions of `± i z`, multiplied back, as `mp-complex.c` composes them
    (`ctanh_mp` overwrites its intermediate result before the last multiplication, so it
    always yields 1). -/
def chypMp (name : String) (r i : MP) (digs : Nat) : MM (MP × MP) := do
  let gdigs := digs + guards
  let re := lenMp r digs gdigs
  let im := lenMp i digs gdigs
  let zero := nil gdigs
  let one := setOne (nil gdigs) gdigs
  let minusOne := setMinusOne (nil gdigs) gdigs
  let (re, im) ← match name with
    | "sinh" => do
      let (a, b) ← lift (cmulMp re im zero one gdigs)
      let (a, b) ← csinCosMp false a b gdigs
      lift (cmulMp a b zero minusOne gdigs)
    | "cosh" => do
      let (a, b) ← lift (cmulMp re im zero one gdigs)
      csinCosMp true a b gdigs
    | "tanh" => do
      let (a, b) ← lift (cmulMp re im zero one gdigs)
      let (a, b) ← ctanMp a b gdigs
      lift (cmulMp (setZero a gdigs) (setMinusOne b gdigs) zero one gdigs)
    | "arcsinh" => do
      let (a, b) ← lift (cmulMp re im zero minusOne gdigs)
      let (a, b) ← casinAcosMp false a b gdigs
      lift (cmulMp a b zero one gdigs)
    | "arccosh" => do
      let (a, b) ← casinAcosMp true re im gdigs
      lift (cmulMp a b zero one gdigs)
    | _ => do  -- arctanh
      let (a, b) ← lift (cmulMp re im zero minusOne gdigs)
      let (a, b) ← catanMp a b gdigs
      lift (cmulMp a b zero one gdigs)
  return (← lift (shortenMp r digs re gdigs), ← lift (shortenMp i digs im gdigs))

-- ## The degree and π-scaled variants

def recOf (f : MP → MP → Nat → MM MP) (z x : MP) (digs : Nat) : MM MP := do
  let r ← f z x digs
  lift (recMp r r digs)

def viaPiOver180 (f : MP → MP → Nat → MM MP) (z x : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x)
  let fct ← piMp (nil digs) .piOver180 digs
  let g ← lift (mulMp (nil digs) x fct digs)
  f z g digs

def times180OverPi (f : MP → MP → Nat → MM MP) (z x : MP) (digs : Nat) : MM MP := do
  lift (catchNaN x)
  let fr ← f (nil digs) x digs
  let g ← piMp (nil digs) .d180OverPi digs
  lift (mulMp z fr g digs)

end A68.MP

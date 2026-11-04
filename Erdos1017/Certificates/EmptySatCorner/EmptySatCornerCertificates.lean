module

public import Erdos1017.Exclusions.Common.E2.EmptySatE2Scalar

/-!
# Certificates for the empty-source saturated corner

The small-delta support, exceptional and radical endpoints are shown positive
from rational Bernstein coefficients, and the exceptional price
`cornerExceptionalPrice` has an exact quadratic identity with positive slope,
positive leading coefficient and positive boundary values.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators unitInterval

namespace Erdos1017.EmptySatCorner

open EmptySatE2

private def clearedBase (δ a N : ℝ) : ℝ :=
  let v := 2 * a - δ + N
  δ ^ 3 * (533 / 1000) - δ ^ 2 * N - 2 * (1 - δ) * v ^ 2 - N ^ 2 / 12 +
    (12 / 25) * ((2 - δ) * v - N / 12) ^ 2

private def clearedSupport (δ a N : ℝ) : ℝ :=
  let v := 2 * a - δ + N
  let e := N - a
  clearedBase δ a N - (4 * (2 - δ) * v + 8 * N) * e / 25 - 8 * e ^ 2 / 25

private def clearedExceptional (δ a N : ℝ) : ℝ :=
  let v := 2 * a - δ + N
  let e := N - a
  clearedBase δ a N + (24 / 25) * δ * ((2 - δ) * v - N / 12) * e +
    (12 / 25) * δ ^ 2 * e ^ 2 - 2 * a * δ * e

private def upperDelta (x : ℝ) : ℝ := 2 / 11 + (21 / 100 - 2 / 11) * x

private def upperNumerator (δ y : ℝ) : ℝ :=
  (7 / 20) * δ + ((19 / 100) * δ - 37 / 1250) * y

private def endpointX (δ A D : ℝ) : ℝ :=
  baseScore δ (467 / 2000) A D + 4 * δ * D * (1 - A - D) - (8 / 25) * D * (D - A)

private def endpointY (δ A D : ℝ) : ℝ :=
  (4 * (2 - δ) * baseDifference A D + 8 * D) / 25 + 4 * δ * D

private theorem clearedSupport_eq (δ A D : ℝ) :
    clearedSupport δ (δ * A) (δ * D) =
      δ ^ 2 * supportScore δ (467 / 2000) A D (D - A) := by
  unfold clearedSupport clearedBase supportScore baseScore baseCredit baseDifference
  ring

private theorem clearedExceptional_eq (δ A D : ℝ) :
    clearedExceptional δ (δ * A) (δ * D) =
      δ ^ 2 * exceptionalBaseScore δ (467 / 2000) A D := by
  unfold clearedExceptional clearedBase exceptionalBaseScore baseScore baseCredit baseDifference
  ring

private theorem tensor2_pos (n m : ℕ)
    (c : Fin (n + 1) → Fin (m + 1) → ℝ) (hc : ∀ i j, 1 ≤ c i j) (x y : I) :
    0 < ∑ i, ∑ j, c i j * (bernstein n i x * bernstein m j y) := by
  have hunit : (∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
      bernstein n i x * bernstein m j y) = 1 := by
    simp_rw [← Finset.mul_sum, bernstein.probability, mul_one]
    exact bernstein.probability _ _
  have hsum : 1 ≤ ∑ i, ∑ j, c i j * (bernstein n i x * bernstein m j y) := by
    rw [← hunit]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right (hc i j)
      (mul_nonneg bernstein_nonneg bernstein_nonneg))
  linarith only [hsum]

private theorem tensor3_pos (n m l : ℕ)
    (c : Fin (n + 1) → Fin (m + 1) → Fin (l + 1) → ℝ)
    (hc : ∀ i j k, 1 ≤ c i j k) (x y z : I) :
    0 < ∑ i, ∑ j, ∑ k,
      c i j k * (bernstein n i x * bernstein m j y * bernstein l k z) := by
  have hunit : (∑ i : Fin (n + 1), ∑ j : Fin (m + 1), ∑ k : Fin (l + 1),
      bernstein n i x * bernstein m j y * bernstein l k z) = 1 := by
    simp_rw [← Finset.mul_sum, bernstein.probability, mul_one]
    simp_rw [← Finset.mul_sum, bernstein.probability, mul_one]
    exact bernstein.probability _ _
  have hsum : 1 ≤ ∑ i, ∑ j, ∑ k,
      c i j k * (bernstein n i x * bernstein m j y * bernstein l k z) := by
    rw [← hunit]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right (hc i j k)
      (mul_nonneg (mul_nonneg bernstein_nonneg bernstein_nonneg) bernstein_nonneg))
  linarith only [hsum]

set_option maxHeartbeats 2000000 in
private theorem support_chart (x y : I) :
    0 < clearedSupport (upperDelta x) ((7 / 20) * upperDelta x)
      (upperNumerator (upperDelta x) y) := by
  let coeff : Fin 5 → Fin 3 → ℝ := fun i j =>
    ![
      ![377580000000000, 272054880000000, 150336142080000],
      ![430503975000000, 290700933600000, 125984480001600],
      ![489832774750000, 311460727842000, 96359951813488],
      ![556136207983125, 334634228007090, 61550298832803],
      ![629984499016950, 360523394181720, 21652837442412]] i j
  have hpos := tensor2_pos 4 2 coeff
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [coeff]) x y
  have hid : (549037500000000000 : ℝ) * (clearedSupport (upperDelta x) ((7 / 20) * upperDelta x)
      (upperNumerator (upperDelta x) y)) =
      ∑ i : Fin 5, ∑ j : Fin 3, coeff i j * (bernstein 4 i x * bernstein 2 j y) := by
    norm_num [clearedSupport, clearedExceptional, clearedBase, upperDelta, upperNumerator,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 2000000 in
private theorem exceptional_lower_chart (x y : I) :
    0 < clearedExceptional (upperDelta x) ((7 / 20) * upperDelta x)
      (upperNumerator (upperDelta x) y) := by
  let coeff : Fin 5 → Fin 3 → ℝ := fun i j =>
    ![
      ![15103200000000, 10981420800000, 6883079731200],
      ![17220159000000, 11712231168000, 6247998504000],
      ![19593310990000, 12492565556240, 5471277870080],
      ![22245448319325, 13326630751830, 4547411558910],
      ![25199379960678, 14218650165258, 3470909923338]] i j
  have hpos := tensor2_pos 4 2 coeff
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [coeff]) x y
  have hid : (21961500000000000 : ℝ) * (clearedExceptional (upperDelta x) ((7 / 20) * upperDelta x)
      (upperNumerator (upperDelta x) y)) =
      ∑ i : Fin 5, ∑ j : Fin 3, coeff i j * (bernstein 4 i x * bernstein 2 j y) := by
    norm_num [clearedSupport, clearedExceptional, clearedBase, upperDelta, upperNumerator,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 2000000 in
private theorem exceptional_upper_chart (x y : I) :
    0 < clearedExceptional (upperDelta x) (upperNumerator (upperDelta x) y)
      (upperNumerator (upperDelta x) y) := by
  let coeff : Fin 5 → Fin 3 → ℝ := fun i j =>
    ![
      ![377580000000000, 275710560000000, 160914635520000],
      ![430503975000000, 295659804000000, 141130704897600],
      ![489832774750000, 317970111602000, 117491835281392],
      ![556136207983125, 342976139110770, 90403165830747],
      ![629984499016950, 371017696078260, 60333735970068]] i j
  have hpos := tensor2_pos 4 2 coeff
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [coeff]) x y
  have hid : (549037500000000000 : ℝ) * (clearedExceptional (upperDelta x) (upperNumerator (upperDelta x) y)
      (upperNumerator (upperDelta x) y)) =
      ∑ i : Fin 5, ∑ j : Fin 3, coeff i j * (bernstein 4 i x * bernstein 2 j y) := by
    norm_num [clearedSupport, clearedExceptional, clearedBase, upperDelta, upperNumerator,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 4000000 in
private theorem endpoint_X_chart (x y z : I) :
    let D := (7 / 20 : ℝ) + (1 / 20) * y
    let E := (D - 7 / 20) * z
    0 < endpointX (upperDelta x) (D - E) D := by
  dsimp only
  let coeff : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k =>
    ![
      ![
        ![293930000, 293930000, 293930000],
        ![240720000, 250335000, 259950000],
        ![169230000, 193350000, 215970000]],
      ![
        ![319719675, 319719675, 319719675],
        ![263914200, 274218175, 284522150],
        ![189245925, 214785725, 238934025]],
      ![
        ![345512233, 345512233, 345512233],
        ![287119932, 298109999, 309100066],
        ![209307978, 236244514, 261909582]]] i j k
  have hpos := tensor3_pos 2 2 2 coeff
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [coeff]) x y z
  have hid : (3025000000 : ℝ) *
      (endpointX (upperDelta x) (((7 / 20 : ℝ) + (1 / 20) * y) - ((((7 / 20 : ℝ) + (1 / 20) * y) - 7 / 20) * z)) ((7 / 20 : ℝ) + (1 / 20) * y)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        coeff i j k * (bernstein 2 i x * bernstein 2 j y * bernstein 2 k z) := by
    norm_num [endpointX, endpointY, upperDelta, baseScore, baseCredit, baseDifference,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 4000000 in
private theorem endpoint_separation_chart (x y z : I) :
    let D := (7 / 20 : ℝ) + (1 / 20) * y
    let E := (D - 7 / 20) * z
    0 < (endpointX (upperDelta x) (D - E) D) ^ 2 -
      (endpointY (upperDelta x) (D - E) D) ^ 2 * D * E := by
  dsimp only
  let coeff : Fin 5 → Fin 5 → Fin 5 → ℝ := fun i j k =>
    ![
      ![
        ![9330643249200000000, 9330643249200000000, 9330643249200000000, 9330643249200000000, 9330643249200000000],
        ![7641521596800000000, 7637151028500000000, 7632780460200000000, 7628409891900000000, 7624039323600000000],
        ![5962824385200000000, 5875441318800000000, 5800502269200000000, 5738007236400000000, 5687956220400000000],
        ![4399600924800000000, 4105761309900000000, 3860383152600000000, 3661772877900000000, 3508236910800000000],
        ![3092989633200000000, 2409100844400000000, 1849402544400000000, 1405805533200000000, 1070463610800000000]],
      ![
        ![10149322039857000000, 10149322039857000000, 10149322039857000000, 10149322039857000000, 10149322039857000000],
        ![8344901932488000000, 8344614496370625000, 8344327060253250000, 8344039624135875000, 8343752188018500000],
        ![6549280564167000000, 6466283837838000000, 6396261571804500000, 6339213766066500000, 6295140420624000000],
        ![4871743873128000000, 4577225677113375000, 4332965409654750000, 4137276848797125000, 3988473772585500000],
        ![3458817491877000000, 2761886607579000000, 2193164999784000000, 1744622192412000000, 1408453132383000000]],
      ![
        ![11015919065156445000, 11015919065156445000, 11015919065156445000, 11015919065156445000, 11015919065156445000],
        ![9091424076265080000, 9095574817866982500, 9099725559468885000, 9103876301070787500, 9108027042672690000],
        ![7174099149154245000, 7096040457062865000, 7031513160601435000, 6980517259769955000, 6943052754568425000],
        ![5377548062791080000, 5082919802746087500, 4840418233438095000, 4648368177307057500, 4505094456792930000],
        ![3853772257505445000, 3144187050089085000, 2566954851774225000, 2114120463894945000, 1777936758659325000]],
      ![
        ![11930442355074701700, 11930442355074701700, 11930442355074701700, 11930442355074701700, 11930442355074701700],
        ![9881107699003417800, 9890049709997661600, 9898991720991905400, 9907933731986149200, 9916875742980393000],
        ![7837321850375494950, 7764745448960047350, 7706284668162846150, 7661939507983891350, 7631709968423182950],
        ![5917083732977293800, 5622899224411450575, 5382784159112334150, 5195078301341072925, 5058121415358795300],
        ![4277953645900882200, 3556080495388773000, 2970830918654557200, 2514342296957713200, 2178943090311695400]],
      ![
        ![12892899940485799212, 12892899940485799212, 12892899940485799212, 12892899940485799212, 12892899940485799212],
        ![10713972475165840848, 10728056892913069842, 10742141310660298836, 10756225728407527830, 10770310146154756824],
        ![8538990392407108392, 8472433096786948344, 8420603734840515504, 8383502306567809872, 8361128811968831448],
        ![6490421180325089568, 6197219515629273780, 5960105743383664488, 5777438671377720468, 5647577107400900496],
        ![4731461602680436272, 3997645381837370736, 3404852076159273168, 2945329669634379984, 2611500742385430192]]] i j k
  have hpos := tensor3_pos 4 4 4 coeff
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [coeff]) x y z
  have hid : (988267500000000000000 : ℝ) *
      ((endpointX (upperDelta x) (((7 / 20 : ℝ) + (1 / 20) * y) - ((((7 / 20 : ℝ) + (1 / 20) * y) - 7 / 20) * z)) ((7 / 20 : ℝ) + (1 / 20) * y)) ^ 2 -
      (endpointY (upperDelta x) (((7 / 20 : ℝ) + (1 / 20) * y) - ((((7 / 20 : ℝ) + (1 / 20) * y) - 7 / 20) * z)) ((7 / 20 : ℝ) + (1 / 20) * y)) ^ 2 * ((7 / 20 : ℝ) + (1 / 20) * y) * ((((7 / 20 : ℝ) + (1 / 20) * y) - 7 / 20) * z)) =
      ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5,
        coeff i j k * (bernstein 4 i x * bernstein 4 j y * bernstein 4 k z) := by
    norm_num [endpointX, endpointY, upperDelta, baseScore, baseCredit, baseDifference,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

private theorem upper_coordinates {δ D : ℝ}
    (hδ : δ ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * δ))) :
    ∃ x y : I, upperDelta x = δ ∧ upperNumerator δ y = δ * D := by
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  let w := 19 / 100 - 37 / (1250 * δ)
  have hid : δ * w = (19 / 100) * δ - 37 / 1250 := by
    dsimp [w]
    field_simp
  have hw : 0 < w := by
    have hp : 0 < δ * w := by rw [hid]; linarith only [hδ.1]
    exact (mul_pos_iff_of_pos_left hδ0).mp hp
  let x : I := ⟨(δ - 2 / 11) / (21 / 100 - 2 / 11), by
    constructor <;> norm_num <;> linarith only [hδ.1, hδ.2]⟩
  let y : I := ⟨(D - 7 / 20) / w, by
    refine ⟨div_nonneg (by linarith only [hD.1]) hw.le, ?_⟩
    apply (div_le_one hw).mpr
    dsimp [w]
    linarith only [hD.2]⟩
  refine ⟨x, y, ?_, ?_⟩
  · dsimp [upperDelta, x]
    ring
  · have hy : w * (y : ℝ) = D - 7 / 20 := by
      dsimp [y]
      rw [mul_div_cancel₀ _ hw.ne']
    have hm := congrArg (fun z : ℝ => δ * z) hy
    have hn := congrArg (fun z : ℝ => z * (y : ℝ)) hid
    dsimp [upperNumerator]
    nlinarith only [hm, hn]

/-- The correlated upper-slope support endpoint is strictly positive.
Its fifteen rational Bernstein coefficients are verified exactly above. -/
theorem small_delta_support_endpoint_pos {δ D : ℝ}
    (hδ : δ ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * δ))) :
    0 < supportScore δ (467 / 2000) (7 / 20) D (D - 7 / 20) := by
  obtain ⟨x, y, hx, hy⟩ := upper_coordinates hδ hD
  have hp := support_chart x y
  rw [hx, hy] at hp
  have hA : (7 / 20) * δ = δ * (7 / 20) := mul_comm _ _
  rw [hA, clearedSupport_eq] at hp
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (by linarith only [hδ.1] : 0 < δ))).mp hp

/-- Both exceptional upper-slope endpoints are paid by the same genuine
deficit parameter, including the upper diagonal endpoint A=D. -/
theorem small_delta_exceptional_endpoints_pos {δ D : ℝ}
    (hδ : δ ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * δ))) :
    0 < exceptionalBaseScore δ (467 / 2000) (7 / 20) D ∧
      0 < exceptionalBaseScore δ (467 / 2000) D D := by
  obtain ⟨x, y, hx, hy⟩ := upper_coordinates hδ hD
  have hlo := exceptional_lower_chart x y
  have hhi := exceptional_upper_chart x y
  rw [hx, hy] at hlo hhi
  have hA : (7 / 20) * δ = δ * (7 / 20) := mul_comm _ _
  rw [hA, clearedExceptional_eq] at hlo
  rw [clearedExceptional_eq] at hhi
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos (by linarith only [hδ.1])
  exact ⟨(mul_pos_iff_of_pos_left hδ2).mp hlo, (mul_pos_iff_of_pos_left hδ2).mp hhi⟩

private theorem endpoint_coordinates {δ D E : ℝ}
    (hδ : δ ∈ Icc (2 / 11 : ℝ) (21 / 100)) (hD : D ∈ Icc (7 / 20 : ℝ) (2 / 5))
    (hE : E ∈ Icc (0 : ℝ) (D - 7 / 20)) :
    ∃ x y z : I, upperDelta x = δ ∧
      (7 / 20 : ℝ) + (1 / 20) * y = D ∧ (D - 7 / 20) * z = E := by
  let x : I := ⟨(δ - 2 / 11) / (21 / 100 - 2 / 11), by
    constructor <;> norm_num <;> linarith only [hδ.1, hδ.2]⟩
  let y : I := ⟨20 * (D - 7 / 20), by
    constructor <;> linarith only [hD.1, hD.2]⟩
  have hx : upperDelta x = δ := by dsimp [upperDelta, x]; ring
  have hy : (7 / 20 : ℝ) + (1 / 20) * y = D := by dsimp [y]; ring
  by_cases hzero : D = 7 / 20
  · have he : E = 0 := by rw [hzero] at hE; linarith only [hE.1, hE.2]
    exact ⟨x, y, 0, hx, hy, by rw [hzero, he]; norm_num⟩
  · have hw : 0 < D - 7 / 20 := sub_pos.mpr (lt_of_le_of_ne hD.1 (Ne.symm hzero))
    let z : I := ⟨E / (D - 7 / 20),
      div_nonneg hE.1 hw.le, (div_le_one hw).mpr hE.2⟩
    refine ⟨x, y, z, hx, hy, ?_⟩
    dsimp [z]
    rw [mul_div_cancel₀ _ hw.ne']

/-- The enlarged upper-strip radical endpoint has positive signed X0
and strictly positive squared separation, including zero E. -/
theorem small_delta_radical_separation {δ D E : ℝ}
    (hδ : δ ∈ Icc (2 / 11 : ℝ) (21 / 100)) (hD : D ∈ Icc (7 / 20 : ℝ) (2 / 5))
    (hE : E ∈ Icc (0 : ℝ) (D - 7 / 20)) :
    let A := D - E
    let v := baseDifference A D
    let p := (4 * (2 - δ) * v + 8 * D) / 25
    let X0 := baseScore δ (467 / 2000) A D + 4 * δ * D * (1 - A - D) - (8 / 25) * D * E
    let Y0 := p + 4 * δ * D
    0 < X0 ∧ Y0 ^ 2 * D * E < X0 ^ 2 := by
  obtain ⟨x, y, z, hx, hy, hz⟩ := endpoint_coordinates hδ hD hE
  have hX := endpoint_X_chart x y z
  have hsep := endpoint_separation_chart x y z
  dsimp only at hX hsep
  rw [hx, hy, hz] at hX hsep
  have he : D - (D - E) = E := by ring
  simp only [endpointX, endpointY, he] at hX hsep
  dsimp only
  exact ⟨hX, by linarith only [hsep]⟩

/-- The original correlated upper bound for the corner deficit. -/
def cornerDeficitCap (δ : ℝ) : ℝ := 336 / 625 - 37 / (1250 * δ)

/-- The original trace slack, with its correlated lower intercept. -/
def cornerTraceSlack (δ A : ℝ) : ℝ :=
  let gamma := (23 / 100) * δ + 37 / 2500
  467 / 1000 - 3 * A ^ 2 - 2 * A * gamma - gamma ^ 2

/-- The joint signed context price after retaining the whole correlated
intercept; E is D minus the original head mass. -/
def cornerPrice (δ A E L : ℝ) : ℝ :=
  let D := A + E
  let v := baseDifference A D
  let K := baseCredit δ A D
  let p := (4 * (2 - δ) * v + 8 * D) / 25
  let gamma := δ * (1 - D) / 2
  let Ubad := 1 - 2 * (1 - δ) * A - 3 * gamma
  37 / 1250 - 2 * (1 - δ) * v ^ 2 - D ^ 2 / 12 + (12 / 25) * K ^ 2 -
    p * L - (8 / 25) * L ^ 2 + 4 * δ * (1 - A - D - L) * (D - Ubad)

private def capNumerator (δ : ℝ) : ℝ := (336 / 625) * δ - 37 / 1250

private def clearedPrice (δ a N l : ℝ) : ℝ :=
  let v := 2 * a - δ + N
  let K := (2 - δ) * v - N / 12
  let p := 4 * (2 - δ) * v + 8 * N
  let U := δ - 2 * (1 - δ) * a - (3 * δ / 2) * (δ - N)
  (37 / 1250) * δ ^ 2 - 2 * (1 - δ) * v ^ 2 - N ^ 2 / 12 +
    (12 / 25) * K ^ 2 - p * l / 25 - (8 / 25) * l ^ 2 +
    4 * δ * (δ - a - N - l) * (N - U)

private def clearedTrace (δ a : ℝ) : ℝ :=
  let gamma := (23 / 100) * δ + 37 / 2500
  (467 / 1000) * δ ^ 2 - 3 * a ^ 2 - 2 * a * δ * gamma - δ ^ 2 * gamma ^ 2

private theorem clearedPrice_eq (δ A E L : ℝ) :
    clearedPrice δ (δ * A) (δ * (A + E)) (δ * L) = δ ^ 2 * cornerPrice δ A E L := by
  unfold clearedPrice cornerPrice baseCredit baseDifference
  ring

private theorem clearedTrace_eq (δ A : ℝ) :
    clearedTrace δ (δ * A) = δ ^ 2 * cornerTraceSlack δ A := by
  unfold clearedTrace cornerTraceSlack
  ring

private theorem capNumerator_eq {δ : ℝ} (hδ : 0 < δ) :
    capNumerator δ = δ * cornerDeficitCap δ := by
  unfold capNumerator cornerDeficitCap
  field_simp

private def remainingDelta (x : ℝ) : ℝ := 21 / 100 + (19 / 100) * x

private def middleDelta (x : ℝ) : ℝ := 37 / 172 + (1 / 4 - 37 / 172) * x

private def smallLPolynomial (x y z : ℝ) : ℝ :=
  let δ := remainingDelta x
  let a := δ * (7 / 20 + y / 40)
  let e := (capNumerator δ - a) * z
  clearedPrice δ a (a + e) e

private def smallEPolynomial (x y z w : ℝ) : ℝ :=
  let δ := remainingDelta x
  let A := 7 / 20 + y / 40
  let E := z / 20
  let L := E + (1 / 10 - E) * w
  δ * cornerPrice δ A E L - (capNumerator δ - δ * (A + E)) / 25 -
    δ * cornerTraceSlack δ A / 6

private def middlePolynomial (x y z w : ℝ) : ℝ :=
  let δ := middleDelta x
  let a := (7 / 20) * δ + (capNumerator δ - (2 / 5) * δ) * y
  let e := δ / 20 + (capNumerator δ - a - δ / 20) * z
  let l := e + (3 * a - δ) * w / 2
  clearedPrice δ a (a + e) l - clearedTrace δ a / 6

private theorem tensor4_pos (n m l r : ℕ)
    (c : Fin (n + 1) → Fin (m + 1) → Fin (l + 1) → Fin (r + 1) → ℝ)
    (hc : ∀ i j k t, 1 ≤ c i j k t) (x y z w : I) :
    0 < ∑ i, ∑ j, ∑ k, ∑ t,
      c i j k t * (bernstein n i x * bernstein m j y * bernstein l k z * bernstein r t w) := by
  have hunit : (∑ i : Fin (n + 1), ∑ j : Fin (m + 1), ∑ k : Fin (l + 1), ∑ t : Fin (r + 1),
      bernstein n i x * bernstein m j y * bernstein l k z * bernstein r t w) = 1 := by
    simp_rw [← Finset.mul_sum, bernstein.probability, mul_one]
    simp_rw [← Finset.mul_sum, bernstein.probability, mul_one]
    simp_rw [← Finset.mul_sum, bernstein.probability, mul_one]
    exact bernstein.probability _ _
  have hsum : 1 ≤ ∑ i, ∑ j, ∑ k, ∑ t,
      c i j k t * (bernstein n i x * bernstein m j y * bernstein l k z * bernstein r t w) := by
    rw [← hunit]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro t _
    exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right (hc i j k t)
      (mul_nonneg (mul_nonneg (mul_nonneg bernstein_nonneg bernstein_nonneg)
        bernstein_nonneg) bernstein_nonneg))
  linarith only [hsum]

set_option maxHeartbeats 6000000 in
private theorem small_L_chart (x y z : I) : 0 < smallLPolynomial x y z := by
  let coeff : Fin 5 → Fin 3 → Fin 3 → ℝ := fun i j k =>
    ![
      ![
        ![91663062750000, 79503164275500, 56806536421776],
        ![95891246718750, 82698570982125, 64616147209776],
        ![94055997656250, 84430160876250, 72535153560276]],
      ![
        ![152837094375000, 125006131807500, 66947820923040],
        ![159818153906250, 127688654694375, 77672118930540],
        ![157411898437500, 128054273831250, 88604789438040]],
      ![
        ![254410275000000, 197458283800000, 65148083281600],
        ![264761937500000, 198297294150000, 79271203081600],
        ![261125625000000, 195620904500000, 93791222881600]],
      ![
        ![423696000000000, 310239012000000, 47641836864000],
        ![436083750000000, 307055121000000, 65588208864000],
        ![428812500000000, 298885230000000, 84290580864000]],
      ![
        ![708240000000000, 474314880000000, 12436546560000],
        ![714600000000000, 463883040000000, 35378626560000],
        ![696000000000000, 447211200000000, 59760706560000]]] i j k
  have hpos := tensor3_pos 4 2 2 coeff
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [coeff]) x y z
  have hid : (46875000000000000 : ℝ) * smallLPolynomial x y z =
      ∑ i : Fin 5, ∑ j : Fin 3, ∑ k : Fin 3, coeff i j k * (bernstein 4 i x * bernstein 2 j y * bernstein 2 k z) := by
    norm_num [smallLPolynomial, clearedPrice, clearedTrace, capNumerator, remainingDelta, middleDelta,
      cornerPrice, cornerTraceSlack, baseDifference, baseCredit,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 6000000 in
private theorem small_E_chart (x y z w : I) : 0 < smallEPolynomial x y z w := by
  let coeff : Fin 4 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k t =>
    ![
      ![
        ![
          ![5128394076, 3489159276, 1366084476],
          ![4326265980, 2752519680, 936853380],
          ![2638698588, 1474760988, 189863388]],
        ![
          ![6214508532, 4284043632, 1869738732],
          ![5075951364, 3283782489, 1249693614],
          ![3051954900, 1742402250, 311889600]],
        ![
          ![6904376172, 4682681172, 1977146172],
          ![5429389932, 3418798482, 1166287032],
          ![3068964396, 1613796696, 37668996]]],
      ![
        ![
          ![8643178464, 6196436064, 3119933664],
          ![7404784224, 5105764224, 2491864224],
          ![4955538144, 3268203744, 1423429344]],
        ![
          ![10147960504, 7288401304, 3799082104],
          ![8433638584, 5825005984, 2901493384],
          ![5508464824, 3614722024, 1563539224]],
        ![
          ![11080341104, 7807965104, 3905829104],
          ![8890091504, 5971846304, 2738721104],
          ![5488990064, 3388838864, 1131247664]]],
      ![
        ![
          ![14789899776, 11152267776, 6738955776],
          ![12759634176, 9447154176, 5746834176],
          ![9197054976, 6793982976, 4196990976]],
        ![
          ![16653501376, 12466845376, 7504509376],
          ![13997776576, 10273528576, 6161440576],
          ![9809738176, 7132154176, 4260650176]],
        ![
          ![17754043376, 13018363376, 7507003376],
          ![14472859376, 10336843376, 5812987376],
          ![9659361776, 6707265776, 3561249776]]],
      ![
        ![
          ![25247723520, 19764203520, 13359083520],
          ![21582059520, 16801259520, 11559659520],
          ![16220651520, 12810731520, 9170411520]],
        ![
          ![27024107520, 20883947520, 13822187520],
          ![22639595520, 17366315520, 11632235520],
          ![16559339520, 12821099520, 8852459520]],
        ![
          ![27932027520, 21135227520, 13416827520],
          ![22828667520, 17062907520, 10836347520],
          ![16029563520, 11963003520, 7666043520]]]] i j k t
  have hpos := tensor4_pos 3 2 2 2 coeff
    (by intro i j k t; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases t <;> norm_num [coeff]) x y z w
  have hid : (720000000000 : ℝ) * smallEPolynomial x y z w =
      ∑ i : Fin 4, ∑ j : Fin 3, ∑ k : Fin 3, ∑ t : Fin 3, coeff i j k t * (bernstein 3 i x * bernstein 2 j y * bernstein 2 k z * bernstein 2 t w) := by
    norm_num [smallEPolynomial, clearedPrice, clearedTrace, capNumerator, remainingDelta, middleDelta,
      cornerPrice, cornerTraceSlack, baseDifference, baseCredit,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 6000000 in
private theorem middle_chart (x y z w : I) : 0 < middlePolynomial x y z w := by
  let coeff : Fin 5 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k t =>
    ![
      ![
        ![
          ![693780564661225, 545878767286225, 390383126911225],
          ![693780564661225, 545878767286225, 390383126911225],
          ![693780564661225, 545878767286225, 390383126911225]],
        ![
          ![693780564661225, 545878767286225, 390383126911225],
          ![693780564661225, 545878767286225, 390383126911225],
          ![693780564661225, 545878767286225, 390383126911225]],
        ![
          ![693780564661225, 545878767286225, 390383126911225],
          ![693780564661225, 545878767286225, 390383126911225],
          ![693780564661225, 545878767286225, 390383126911225]]],
      ![
        ![
          ![812107259926375, 649199400301375, 478081980676375],
          ![760011473194375, 594683197824625, 421145362454875],
          ![707915686462375, 540166995347875, 364208744233375]],
        ![
          ![831083995794775, 639307195758025, 436779155945275],
          ![805036102428775, 612049094519650, 408310846834525],
          ![778988209062775, 584790993281275, 379842537723775]],
        ![
          ![850060731663175, 629414991214675, 395476331214175],
          ![850060731663175, 629414991214675, 395476331214175],
          ![850060731663175, 629414991214675, 395476331214175]]],
      ![
        ![
          ![948233038868425, 768942211493425, 580792825118425],
          ![835741343276425, 651309270630925, 458018638985425],
          ![715830912025417, 526257594109417, 327825717193417]],
        ![
          ![988443823194025, 746779856938525, 490899195939025],
          ![926539119477385, 681224370998059, 421692927774733],
          ![864634415760745, 615668885057593, 352486659610441]],
        ![
          ![1015293242425225, 703906289512585, 370675953870793],
          ![1015293242425225, 703906289512585, 370675953870793],
          ![1015293242425225, 703906289512585, 370675953870793]]],
      ![
        ![
          ![1104440651722375, 907273230097375, 700564968472375],
          ![922255449670375, 716925779795125, 502055269919875],
          ![717433085816647, 503941167691147, 280908409565647]],
        ![
          ![1167662932573975, 869559804185725, 553466467893475],
          ![1059087971108167, 753624333437320, 430170487862473],
          ![950513009642359, 637688862688915, 306874507831471]],
        ![
          ![1189295089004455, 767527042026907, 312513762517903],
          ![1189295089004455, 767527042026907, 312513762517903],
          ![1189295089004455, 767527042026907, 312513762517903]]],
      ![
        ![
          ![1283223792973225, 1066557279598225, 839634363223225],
          ![1020823978621225, 792680550289225, 554280718957225],
          ![712675027405993, 473054684116993, 223177937827993]],
        ![
          ![1370411423595625, 1008729628203625, 624976053555625],
          ![1203481818621481, 829450862735749, 433348127594017],
          ![1036552213647337, 650172097267873, 241720201632409]],
        ![
          ![1372150253134633, 818876962524481, 218105202955417],
          ![1372150253134633, 818876962524481, 218105202955417],
          ![1372150253134633, 818876962524481, 218105202955417]]]] i j k t
  have hpos := tensor4_pos 4 2 2 2 coeff
    (by intro i j k t; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases t <;> norm_num [coeff]) x y z w
  have hid : (820512240000000000 : ℝ) * middlePolynomial x y z w =
      ∑ i : Fin 5, ∑ j : Fin 3, ∑ k : Fin 3, ∑ t : Fin 3, coeff i j k t * (bernstein 4 i x * bernstein 2 j y * bernstein 2 k z * bernstein 2 t w) := by
    norm_num [middlePolynomial, clearedPrice, clearedTrace, capNumerator, remainingDelta, middleDelta,
      cornerPrice, cornerTraceSlack, baseDifference, baseCredit,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

private theorem interval_parameter {a b v : ℝ} (hv : v ∈ Icc a b) :
    ∃ x : I, a + (b - a) * x = v := by
  by_cases heq : a = b
  · have he : v = a := by rw [← heq] at hv; linarith only [hv.1, hv.2]
    exact ⟨0, by rw [he]; norm_num⟩
  · have hw : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (hv.1.trans hv.2) heq)
    let x : I := ⟨(v - a) / (b - a),
      div_nonneg (sub_nonneg.mpr hv.1) hw.le,
      (div_le_one hw).mpr (by linarith only [hv.2])⟩
    refine ⟨x, ?_⟩
    change a + (b - a) * ((v - a) / (b - a)) = v
    rw [mul_div_cancel₀ _ hw.ne']
    ring

/-- The small-L joint price is positive on its whole correlated prism,
including every vanishing-width boundary. -/
theorem small_L_price_pos {δ A E : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5)) (hA : A ∈ Icc (7 / 20 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A)) :
    0 < cornerPrice δ A E E := by
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  obtain ⟨x, hx⟩ := interval_parameter hδ
  obtain ⟨y, hy⟩ := interval_parameter hA
  obtain ⟨z, hz⟩ := interval_parameter hE
  have hx' : remainingDelta x = δ := by dsimp [remainingDelta]; nlinarith only [hx]
  have hy' : (7 / 20 : ℝ) + (y : ℝ) / 40 = A := by nlinarith only [hy]
  simp only [sub_zero, zero_add] at hz
  have hc := capNumerator_eq hδ0
  have he : (capNumerator δ - δ * A) * z = δ * E := by
    rw [hc]
    linear_combination δ * hz
  have hp := small_L_chart x y z
  dsimp only [smallLPolynomial] at hp
  rw [hx', hy', he, show δ * A + δ * E = δ * (A + E) by ring, clearedPrice_eq] at hp
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hδ0)).mp hp

/-- The small-E price retains both the deficit-cap correlation and the
original trace slack before its exact positive certificate is applied. -/
theorem small_E_corrected_price_pos {δ A E L : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5)) (hA : A ∈ Icc (7 / 20 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (1 / 20)) (hL : L ∈ Icc E (1 / 10)) :
    0 < cornerPrice δ A E L - (cornerDeficitCap δ - (A + E)) / 25 -
      cornerTraceSlack δ A / 6 := by
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  obtain ⟨x, hx⟩ := interval_parameter hδ
  obtain ⟨y, hy⟩ := interval_parameter hA
  obtain ⟨z, hz⟩ := interval_parameter hE
  obtain ⟨w, hw⟩ := interval_parameter hL
  have hx' : remainingDelta x = δ := by dsimp [remainingDelta]; nlinarith only [hx]
  have hy' : (7 / 20 : ℝ) + (y : ℝ) / 40 = A := by nlinarith only [hy]
  have hz' : (z : ℝ) / 20 = E := by nlinarith only [hz]
  have hp := small_E_chart x y z w
  dsimp only [smallEPolynomial] at hp
  rw [hx', hy', hz', hw] at hp
  have hc := capNumerator_eq hδ0
  have he : δ * (cornerPrice δ A E L - (cornerDeficitCap δ - (A + E)) / 25 -
      cornerTraceSlack δ A / 6) = δ * cornerPrice δ A E L -
        (capNumerator δ - δ * (A + E)) / 25 - δ * cornerTraceSlack δ A / 6 := by
    rw [hc]
    ring
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left hδ0).mp hp

/-- The middle-deficit prism retains the trace correction and both
correlated vanishing widths; all 135 coefficients are proved positive. -/
theorem middle_delta_corrected_price_pos {δ A E L : ℝ}
    (hδ : δ ∈ Icc (37 / 172 : ℝ) (1 / 4))
    (hA : A ∈ Icc (7 / 20 : ℝ) (cornerDeficitCap δ - 1 / 20))
    (hE : E ∈ Icc (1 / 20 : ℝ) (cornerDeficitCap δ - A))
    (hL : L ∈ Icc E (E + (3 * A - 1) / 2)) :
    0 < cornerPrice δ A E L - cornerTraceSlack δ A / 6 := by
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  obtain ⟨x, hx⟩ := interval_parameter hδ
  obtain ⟨y, hy⟩ := interval_parameter hA
  obtain ⟨z, hz⟩ := interval_parameter hE
  obtain ⟨w, hw⟩ := interval_parameter hL
  have hx' : middleDelta x = δ := hx
  have hc := capNumerator_eq hδ0
  have ha : (7 / 20) * δ + (capNumerator δ - (2 / 5) * δ) * y = δ * A := by
    rw [hc]
    linear_combination δ * hy
  have he : δ / 20 + (capNumerator δ - δ * A - δ / 20) * z = δ * E := by
    rw [hc]
    linear_combination δ * hz
  have hl : δ * E + (3 * (δ * A) - δ) * w / 2 = δ * L := by
    linear_combination δ * hw
  have hp := middle_chart x y z w
  dsimp only [middlePolynomial] at hp
  rw [hx', ha, he, hl, show δ * A + δ * E = δ * (A + E) by ring,
    clearedPrice_eq, clearedTrace_eq] at hp
  have hprod : 0 < δ ^ 2 * (cornerPrice δ A E L - cornerTraceSlack δ A / 6) := by
    nlinarith only [hp]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hδ0)).mp hprod

/-- The common-region cap obtained from a genuinely negative original point. -/
def cornerBadCap (δ A E : ℝ) : ℝ :=
  1 - 2 * (1 - δ) * A - 3 * δ * (1 - (A + E)) / 2

/-- The exceptional signed price after the single correlated intercept
is retained. It is the literal F(L,r) of the original context argument. -/
def cornerExceptionalPrice (δ A E L r : ℝ) : ℝ :=
  let D := A + E
  let v := baseDifference A D
  let K := baseCredit δ A D
  37 / 1250 + δ * r - 2 * (1 - δ) * (v - r) ^ 2 +
    (1 - 2 * D + 2 * r) * δ * r - (D - r) ^ 2 / 12 +
    (12 / 25) * (K + δ * E + (δ - 23 / 12) * r) ^ 2 - 2 * A * δ * (E + r) +
    4 * δ * (1 - A - D - L) * (D - cornerBadCap δ A E - r)

/-- The actual linear coefficient of F(Lmax,r), with Lmax=2-5A-E. -/
def cornerExceptionalSlope (δ A E : ℝ) : ℝ :=
  let D := A + E
  let v := baseDifference A D
  2 * δ * (1 - D - A) + (8 - 6 * δ - 24 * δ ^ 2) * v / 25 +
    (8 - 2 * δ) * D / 25 - δ * (46 - 24 * δ) * E / 25 - 4 * δ * (3 * A - 1)

/-- The exceptional price is the original genuine-deficit score with
only its initial correlated intercept replaced. -/
theorem cornerExceptionalPrice_eq_score (δ h A E L r : ℝ) :
    cornerExceptionalPrice δ A E L r = exceptionalScore δ h A (A + E) r -
      δ * (1 - (A + E) + r - 2 * h) + 37 / 1250 + δ * r +
      4 * δ * (1 - A - (A + E) - L) * (A + E - cornerBadCap δ A E - r) := by
  unfold cornerExceptionalPrice exceptionalScore rawExceptionalScore
  ring

/-- This exact quadratic identity licenses every later monotonicity
argument; its slope is derived from the displayed price. -/
theorem cornerExceptionalPrice_quadratic (δ A E r : ℝ) :
    cornerExceptionalPrice δ A E (2 - 5 * A - E) r =
      cornerExceptionalPrice δ A E (2 - 5 * A - E) 0 + cornerExceptionalSlope δ A E * r +
        ((12 * δ ^ 2 + 54 * δ - 8) / 25) * r ^ 2 := by
  unfold cornerExceptionalPrice cornerExceptionalSlope baseCredit baseDifference
  ring

private def clearedExceptionalPrice (δ a N l r : ℝ) : ℝ :=
  let v := 2 * a - δ + N
  let K := (2 - δ) * v - N / 12
  let U := δ - 2 * (1 - δ) * a - (3 * δ / 2) * (δ - N)
  (37 / 1250) * δ ^ 2 + δ ^ 2 * r - 2 * (1 - δ) * (v - r) ^ 2 +
    δ * (δ - 2 * N + 2 * r) * r - (N - r) ^ 2 / 12 +
    (12 / 25) * (K + δ * (N - a) + (δ - 23 / 12) * r) ^ 2 -
    2 * a * δ * (N - a + r) + 4 * δ * (δ - a - N - l) * (N - U - r)

private theorem clearedExceptionalPrice_eq (δ A E L r : ℝ) :
    clearedExceptionalPrice δ (δ * A) (δ * (A + E)) (δ * L) (δ * r) =
      δ ^ 2 * cornerExceptionalPrice δ A E L r := by
  unfold clearedExceptionalPrice cornerExceptionalPrice cornerBadCap baseCredit baseDifference
  ring

private def exceptionalA (y : ℝ) : ℝ := 3507 / 10000 + (243 / 10000) * y

private def exceptionalN (δ A z : ℝ) : ℝ := δ * A + (capNumerator δ - δ * A) * z

private def badGap (δ A N : ℝ) : ℝ :=
  (3 - 2 * δ) * A - 1 + (3 / 2) * (δ - N)

private def badRemainder (δ A N : ℝ) : ℝ := 27 / 50 + badGap δ A N - A

private def exceptionalWidthPolynomial (x y : ℝ) : ℝ :=
  capNumerator (remainingDelta x) - remainingDelta x * exceptionalA y

private def exceptionalGapPolynomial (x y z : ℝ) : ℝ :=
  badGap (remainingDelta x) (exceptionalA y) (exceptionalN (remainingDelta x) (exceptionalA y) z)

private def exceptionalRemainderPolynomial (x y z : ℝ) : ℝ :=
  badRemainder (remainingDelta x) (exceptionalA y) (exceptionalN (remainingDelta x) (exceptionalA y) z)

private def exceptionalTangentPolynomial (x y z : ℝ) : ℝ :=
  let δ := remainingDelta x
  let A := exceptionalA y
  let N := exceptionalN δ A z
  8 * N * badGap δ A N - δ * badRemainder δ A N

private def exceptionalSquarePolynomial (x y z : ℝ) : ℝ :=
  let δ := remainingDelta x
  let A := exceptionalA y
  (2 - δ) * (3 * A - 1) - (exceptionalN δ A z - δ * A) - A / 12

private def exceptionalSlopePolynomial (x y z : ℝ) : ℝ :=
  let δ := remainingDelta x
  let A := exceptionalA y
  let a := δ * A
  let N := exceptionalN δ A z
  let e := N - a
  2 * δ * (δ - N - a) + (8 - 6 * δ - 24 * δ ^ 2) * (3 * a - δ + e) / 25 +
    (8 - 2 * δ) * N / 25 - δ * (46 - 24 * δ) * e / 25 - 4 * δ ^ 2 * (3 * A - 1)

private def exceptionalPricePolynomial (x y z w : ℝ) : ℝ :=
  let δ := remainingDelta x
  let a := δ * exceptionalA y
  let N := exceptionalN δ (exceptionalA y) z
  let e := N - a
  let r := (2 * δ - 5 * a - 2 * e) * w / 6
  clearedExceptionalPrice δ a N (e + 6 * r) r

private theorem tensor3_nonneg (n m l : ℕ)
    (c : Fin (n + 1) → Fin (m + 1) → Fin (l + 1) → ℝ)
    (hc : ∀ i j k, 0 ≤ c i j k) (x y z : I) :
    0 ≤ ∑ i, ∑ j, ∑ k,
      c i j k * (bernstein n i x * bernstein m j y * bernstein l k z) := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hc i j k)
    (mul_nonneg (mul_nonneg bernstein_nonneg bernstein_nonneg) bernstein_nonneg)

set_option maxHeartbeats 8000000 in
private theorem exceptional_width_chart (x y : I) : 0 < exceptionalWidthPolynomial x y := by
  let coeff : Fin 2 → Fin 2 → ℝ := fun i j =>
    ![
      ![9649, 4546],
      ![45160, 35440]] i j
  have hpos := tensor2_pos 1 1 coeff
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [coeff]) x y
  have hid : (1000000 : ℝ) * exceptionalWidthPolynomial x y =
      ∑ i : Fin 2, ∑ j : Fin 2, coeff i j * (bernstein 1 i x * bernstein 1 j y) := by
    norm_num [exceptionalWidthPolynomial, clearedExceptionalPrice, capNumerator, remainingDelta, exceptionalA,
      exceptionalN, badGap, badRemainder,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 8000000 in
private theorem exceptional_gap_chart (x y z : I) : (4669 / 50000 : ℝ) ≤ exceptionalGapPolynomial x y z := by
  let coeff : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k =>
    ![
      ![
        ![31911, 2964],
        ![141990, 128352]],
      ![
        ![135480, 0],
        ![213240, 106920]]] i j k
  have hpos := tensor3_nonneg 1 1 1 coeff
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [coeff]) x y z
  have hid : (2000000 : ℝ) * (exceptionalGapPolynomial x y z - 4669 / 50000) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, coeff i j k * (bernstein 1 i x * bernstein 1 j y * bernstein 1 k z) := by
    norm_num [exceptionalGapPolynomial, clearedExceptionalPrice, capNumerator, remainingDelta, exceptionalA,
      exceptionalN, badGap, badRemainder,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  have h := (mul_nonneg_iff_of_pos_left (by norm_num)).mp hpos
  linarith only [h]

set_option maxHeartbeats 8000000 in
private theorem exceptional_remainder_chart (x y z : I) : (7067 / 25000 : ℝ) ≤ exceptionalRemainderPolynomial x y z := by
  let coeff : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k =>
    ![
      ![
        ![31911, 2964],
        ![93390, 79752]],
      ![
        ![135480, 0],
        ![164640, 58320]]] i j k
  have hpos := tensor3_nonneg 1 1 1 coeff
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [coeff]) x y z
  have hid : (2000000 : ℝ) * (exceptionalRemainderPolynomial x y z - 7067 / 25000) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, coeff i j k * (bernstein 1 i x * bernstein 1 j y * bernstein 1 k z) := by
    norm_num [exceptionalRemainderPolynomial, clearedExceptionalPrice, capNumerator, remainingDelta, exceptionalA,
      exceptionalN, badGap, badRemainder,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  have h := (mul_nonneg_iff_of_pos_left (by norm_num)).mp hpos
  linarith only [h]

set_option maxHeartbeats 8000000 in
private theorem exceptional_tangent_chart (x y z : I) : 0 < exceptionalTangentPolynomial x y z := by
  let coeff : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k =>
    ![
      ![
        ![852198774, 1590154294, 1769490608],
        ![8461241250, 9461275915, 10198124456],
        ![17193750000, 17972252500, 18626758304]],
      ![
        ![6146577160, 8121474860, 7481879520],
        ![16696150000, 19606816400, 20875709040],
        ![28712500000, 31974350000, 34269538560]],
      ![
        ![20323654400, 22644878400, 12729548800],
        ![32906000000, 36074808000, 29640793600],
        ![47000000000, 50544000000, 46552038400]]] i j k
  have hpos := tensor3_pos 2 2 2 coeff
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [coeff]) x y z
  have hid : (500000000000 : ℝ) * exceptionalTangentPolynomial x y z =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, coeff i j k * (bernstein 2 i x * bernstein 2 j y * bernstein 2 k z) := by
    norm_num [exceptionalTangentPolynomial, clearedExceptionalPrice, capNumerator, remainingDelta, exceptionalA,
      exceptionalN, badGap, badRemainder,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 8000000 in
private theorem exceptional_square_chart (x y z : I) : 0 < exceptionalSquarePolynomial x y z := by
  let coeff : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k =>
    ![
      ![
        ![64034, 54385],
        ![192500, 187954]],
      ![
        ![54135, 8975],
        ![168750, 133310]]] i j k
  have hpos := tensor3_pos 1 1 1 coeff
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [coeff]) x y z
  have hid : (1000000 : ℝ) * exceptionalSquarePolynomial x y z =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, coeff i j k * (bernstein 1 i x * bernstein 1 j y * bernstein 1 k z) := by
    norm_num [exceptionalSquarePolynomial, clearedExceptionalPrice, capNumerator, remainingDelta, exceptionalA,
      exceptionalN, badGap, badRemainder,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 8000000 in
private theorem exceptional_slope_chart (x y z : I) : 0 < exceptionalSlopePolynomial x y z := by
  let coeff : Fin 4 → Fin 2 → Fin 2 → ℝ := fun i j k =>
    ![
      ![
        ![3933969921, 3722656821],
        ![2797751250, 2698193850]],
      ![
        ![5528424290, 4819550590],
        ![3503862500, 3066492700]],
      ![
        ![7480189600, 5396633600],
        ![4057000000, 2518736000]],
      ![
        ![9757104000, 5421744000],
        ![4380000000, 977760000]]] i j k
  have hpos := tensor3_pos 3 1 1 coeff
    (by intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [coeff]) x y z
  have hid : (93750000000 : ℝ) * exceptionalSlopePolynomial x y z =
      ∑ i : Fin 4, ∑ j : Fin 2, ∑ k : Fin 2, coeff i j k * (bernstein 3 i x * bernstein 1 j y * bernstein 1 k z) := by
    norm_num [exceptionalSlopePolynomial, clearedExceptionalPrice, capNumerator, remainingDelta, exceptionalA,
      exceptionalN, badGap, badRemainder,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 8000000 in
private theorem exceptional_price_chart (x y z w : I) : 0 < exceptionalPricePolynomial x y z w := by
  let coeff : Fin 5 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k t =>
    ![
      ![
        ![
          ![26465785148377008, 19638185302343538, 18030577739988618],
          ![22849101017909208, 16730565018498765, 13886007372690012],
          ![17911673498695608, 12922422643621692, 9986610505951158]],
        ![
          ![27601879606560000, 21031892667292500, 17108960638612500],
          ![24061598650454400, 18417706062635754, 14469037655106888],
          ![19899066741375600, 15379250266784808, 11944624955935884]],
        ![
          ![27088127325000000, 22180570453125000, 18615333515625000],
          ![24555008614500000, 20362695305872500, 17047773442350000],
          ![21728724515647200, 18344931284833200, 15534634526975832]]],
      ![
        ![
          ![44127554127491520, 31506332645966220, 27724784731573545],
          ![35404006937350320, 24741561528040050, 18273059889907755],
          ![22872050775064620, 15412018320714780, 9735519976802445]],
        ![
          ![46008224280900000, 34182670112325000, 26839709030531250],
          ![36954609326067600, 27630462530442960, 20159536643436270],
          ![25622043148042200, 19539434296019520, 14000041092288810]],
        ![
          ![45334626750000000, 36586708593750000, 30111910664062500],
          ![37392264954000000, 31001077561275000, 25410952786687500],
          ![28147859581518000, 24534758547104400, 20997693442084980]]],
      ![
        ![
          ![73433952439948800, 50339508583876800, 41937393791234800],
          ![54331448799052800, 36325847862120000, 23152255848221200],
          ![25760918872756800, 16060538236435200, 7573212002282800]],
        ![
          ![76222114776000000, 55197080718000000, 41622517787500000],
          ![56199598741728000, 41312992337270400, 27894987405800800],
          ![29501776252656000, 23004792576748800, 16291843219890400]],
        ![
          ![75204180000000000, 59819347500000000, 48212644375000000],
          ![56406190320000000, 47154969156000000, 38150651725000000],
          ![32945564916000000, 31386162016512000, 29466799178987200]]],
      ![
        ![
          ![122219798787072000, 80441887797792000, 62479813610712000],
          ![82017610826112000, 52834157367120000, 28307390486088000],
          ![23741466891552000, 13669203113568000, 4211088816312000]],
        ![
          ![125533484640000000, 88700733720000000, 63944979150000000],
          ![84073835364480000, 61381502846496000, 38676562946832000],
          ![28799363626560000, 25233637879872000, 20904891425136000]],
        ![
          ![123498000000000000, 96885450000000000, 76397137500000000],
          ![83779747200000000, 71352370440000000, 57714741300000000],
          ![33509672438400000, 39080071797120000, 44593269635808000]]],
      ![
        ![
          ![204070058311680000, 129485749524480000, 92163769025280000],
          ![120068469780480000, 75476883801600000, 34014426405120000],
          ![14041084769280000, 7077831045120000, 377347956480000]],
        ![
          ![205654809600000000, 142302988800000000, 97846872000000000],
          ![121970332569600000, 89684906711040000, 54247447457280000],
          ![21000775219200000, 25773905479680000, 29884396746240000]],
        ![
          ![200448000000000000, 155376000000000000, 119886000000000000],
          ![120835584000000000, 106052025600000000, 87267024000000000],
          ![27658437120000000, 47865760358400000, 69744086277120000]]]] i j k t
  have hpos := tensor4_pos 4 2 2 2 coeff
    (by intro i j k t; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases t <;> norm_num [coeff]) x y z w
  have hid : (13500000000000000000 : ℝ) * exceptionalPricePolynomial x y z w =
      ∑ i : Fin 5, ∑ j : Fin 3, ∑ k : Fin 3, ∑ t : Fin 3, coeff i j k t * (bernstein 4 i x * bernstein 2 j y * bernstein 2 k z * bernstein 2 t w) := by
    norm_num [exceptionalPricePolynomial, clearedExceptionalPrice, capNumerator, remainingDelta, exceptionalA,
      exceptionalN, badGap, badRemainder,
      coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

private theorem exceptional_coordinates {δ A E : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (3507 / 10000 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A)) :
    ∃ x y z : I, remainingDelta x = δ ∧ exceptionalA y = A ∧
      exceptionalN δ A z = δ * (A + E) := by
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  obtain ⟨x, hx⟩ := interval_parameter hδ
  obtain ⟨y, hy⟩ := interval_parameter hA
  obtain ⟨z, hz⟩ := interval_parameter hE
  have hx' : remainingDelta x = δ := by dsimp [remainingDelta]; nlinarith only [hx]
  have hy' : exceptionalA y = A := by dsimp [exceptionalA]; nlinarith only [hy]
  simp only [sub_zero, zero_add] at hz
  have hc := capNumerator_eq hδ0
  refine ⟨x, y, z, hx', hy', ?_⟩
  unfold exceptionalN
  rw [hc]
  linear_combination δ * hz

private theorem badGap_eq (δ A E : ℝ) :
    badGap δ A (δ * (A + E)) = A - cornerBadCap δ A E := by
  unfold badGap cornerBadCap
  ring

private theorem badRemainder_eq (δ A E : ℝ) :
    badRemainder δ A (δ * (A + E)) = 1 - cornerBadCap δ A E - 23 / 50 := by
  unfold badRemainder badGap cornerBadCap
  ring

/-- The complete exceptional prism supplies its actual width, both
closed rational bad-region bounds, tangent gap and active support square. -/
theorem exceptional_guards {δ A E : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (3507 / 10000 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A)) :
    A < cornerDeficitCap δ ∧
      4669 / 50000 ≤ A - cornerBadCap δ A E ∧
      7067 / 25000 ≤ 1 - cornerBadCap δ A E - 23 / 50 ∧
      1 - cornerBadCap δ A E - 23 / 50 < 8 * (A + E) * (A - cornerBadCap δ A E) ∧
      0 < (2 - δ) * (3 * A - 1) - δ * E - A / 12 := by
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  obtain ⟨x, y, z, hx, hy, hz⟩ := exceptional_coordinates hδ hA hE
  have hwidth := exceptional_width_chart x y
  dsimp only [exceptionalWidthPolynomial] at hwidth
  rw [hx, hy, capNumerator_eq hδ0] at hwidth
  have hwidth' : A < cornerDeficitCap δ := by
    have hprod : 0 < δ * (cornerDeficitCap δ - A) := by nlinarith only [hwidth]
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hδ0).mp hprod)
  have hgap := exceptional_gap_chart x y z
  dsimp only [exceptionalGapPolynomial] at hgap
  rw [hx, hy, hz, badGap_eq] at hgap
  have hrem := exceptional_remainder_chart x y z
  dsimp only [exceptionalRemainderPolynomial] at hrem
  rw [hx, hy, hz, badRemainder_eq] at hrem
  have htangent := exceptional_tangent_chart x y z
  dsimp only [exceptionalTangentPolynomial] at htangent
  rw [hx, hy, hz, badGap_eq, badRemainder_eq] at htangent
  have htangent' : 1 - cornerBadCap δ A E - 23 / 50 <
      8 * (A + E) * (A - cornerBadCap δ A E) := by
    have hprod : 0 < δ * (8 * (A + E) * (A - cornerBadCap δ A E) -
        (1 - cornerBadCap δ A E - 23 / 50)) := by nlinarith only [htangent]
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hδ0).mp hprod)
  have hsquare := exceptional_square_chart x y z
  dsimp only [exceptionalSquarePolynomial] at hsquare
  rw [hx, hy, hz] at hsquare
  have hsquare' : 0 < (2 - δ) * (3 * A - 1) - δ * E - A / 12 := by
    nlinarith only [hsquare]
  exact ⟨hwidth', hgap, hrem, htangent', hsquare'⟩

/-- The actual linear coefficient of F(Lmax,r) is strictly positive
throughout the exceptional prism. -/
theorem exceptional_slope_pos {δ A E : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (3507 / 10000 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A)) :
    0 < cornerExceptionalSlope δ A E := by
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  obtain ⟨x, y, z, hx, hy, hz⟩ := exceptional_coordinates hδ hA hE
  have hp := exceptional_slope_chart x y z
  dsimp only [exceptionalSlopePolynomial] at hp
  rw [hx, hy, hz] at hp
  have hprod : 0 < δ * cornerExceptionalSlope δ A E := by
    convert hp using 1
    unfold cornerExceptionalSlope baseDifference
    ring
  exact (mul_pos_iff_of_pos_left hδ0).mp hprod

/-- The displayed exceptional quadratic has positive leading coefficient
on the entire remaining-deficit interval. -/
theorem exceptional_quadratic_coefficient_pos {δ : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5)) :
    0 < (12 * δ ^ 2 + 54 * δ - 8) / 25 := by
  nlinarith [hδ.1, sq_nonneg δ]

/-- The full boundary F(E+6r,r) is paid for every legal r, including
zero and degenerate endpoints, whatever the sign of the width. -/
theorem exceptional_boundary_price_pos {δ A E r : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (3507 / 10000 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A))
    (hr : r ∈ Icc (0 : ℝ) ((2 - 5 * A - 2 * E) / 6)) :
    0 < cornerExceptionalPrice δ A E (E + 6 * r) r := by
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  obtain ⟨x, y, z, hx, hy, hz⟩ := exceptional_coordinates hδ hA hE
  obtain ⟨w, hw⟩ := interval_parameter hr
  simp only [sub_zero, zero_add] at hw
  have he : δ * (A + E) - δ * A = δ * E := by ring
  have hr' : (2 * δ - 5 * (δ * A) - 2 * (δ * E)) * w / 6 = δ * r := by
    linear_combination δ * hw
  have hL : δ * E + 6 * (δ * r) = δ * (E + 6 * r) := by ring
  have hp := exceptional_price_chart x y z w
  dsimp only [exceptionalPricePolynomial] at hp
  rw [hx, hy, hz, he, hr', hL, clearedExceptionalPrice_eq] at hp
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hδ0)).mp hp

end Erdos1017.EmptySatCorner

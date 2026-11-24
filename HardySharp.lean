module
public import HardyCompression
public import HardyBornBridge

@[expose] public section
namespace HardyCompression
open Matrix
noncomputable section

def pairWeight (x y : ℝ) : ℝ := ((x*y^5-y*x^5)/(x^5+y^5))^2

def bestTwo (b c : ℝ) : ℝ := max (pairWeight b c) (pairWeight b 1 + pairWeight c 1)

private def join (U V : Block 2 2) : HardyBornBridge.Frame :=
  ![U 0,U 1,V 0,V 1]

private theorem join_moment (U V : Block 2 2) (b c : ℝ) (j : ℕ) :
    HardyBornBridge.G (join U V) ![b,c,1,1] j = moment ![b,c] j U V := by
  ext i l
  simp [HardyBornBridge.G, HardyBornBridge.gram, moment, join, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four, Fin.sum_univ_two, Matrix.diagonal]
  ring

private theorem join_gram (U V : Block 2 2) (h : frame U V) :
    HardyBornBridge.gram (join U V) 1 = 1 := by
  unfold frame at h
  rw [← h]
  ext i l
  simp [HardyBornBridge.gram,join, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_four, Fin.sum_univ_two]
  ring

theorem two_upper {m r : ℕ} (b c : ℝ) (hb : 0<b) (hc : 0<c)
    (Z : Block 2 r) (Y : Block m r) (h : frame Z Y) :
    powerScore 1 5 ![b,c] Z Y ≤ bestTwo b c := by
  obtain ⟨U,V,hUV,_,same⟩ := compress_frame Z Y h
  have hd : ∀ i : Fin 2, 0 < (![b,c] : Fin 2 → ℝ) i := by intro i; fin_cases i <;> assumption
  have h4 : ∀ i : Fin 4, 0 < (![b,c,1,1] : Fin 4 → ℝ) i := by
    intro i; fin_cases i <;> first | assumption | exact zero_lt_one
  have bound := HardyBornBridge.gram_residual_le_matching (join U V) (join_gram U V hUV) _ h4
  rw [← same 1 5 _ hd]
  simpa [powerScore, join_moment,HardyFourPairing.matchingMax,HardyTripleGap.edge,bestTwo,pairWeight]
    using bound

private def coeff (x y : ℝ) : ℂ := (Real.sqrt (y^5 / (x^5+y^5)) : ℝ)
private def lineMoment (x y : ℝ) (j : ℕ) : ℝ := (x^j*y^5+y^j*x^5)/(x^5+y^5)

private theorem coeff_sq {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    coeff x y * coeff x y = ((y^5/(x^5+y^5) : ℝ) : ℂ) := by
  unfold coeff
  rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (by positivity)]
private theorem star_coeff (x y : ℝ) : star (coeff x y) = coeff x y := by simp [coeff]

private theorem line_calc {x y : ℝ} (hx : 0<x) (hy : 0<y) (j : ℕ) :
    coeff x y * ((x^j : ℝ) : ℂ) * coeff x y +
    coeff y x * ((y^j : ℝ) : ℂ) * coeff y x = (lineMoment x y j : ℂ) := by
  rw [mul_right_comm, mul_right_comm (coeff y x), coeff_sq hx hy, coeff_sq hy hx]
  push_cast
  simp only [lineMoment, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [add_comm ((y:ℂ)^5)]; ring

private theorem line_zero {x y : ℝ} (hx : 0<x) (hy : 0<y) : lineMoment x y 0 = 1 := by
  have hn : x^5+y^5 ≠ 0 := by positivity
  simp [lineMoment,add_comm (y^5),hn]
private theorem line_ten {x y : ℝ} (hx : 0<x) (hy : 0<y) : lineMoment x y 10 = x^5*y^5 := by
  unfold lineMoment
  field_simp
private theorem line_value {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    lineMoment x y 2 - (lineMoment x y 10)⁻¹ * (lineMoment x y 6)^2 = pairWeight x y := by
  rw [line_ten hx hy]
  unfold lineMoment pairWeight
  field_simp
  ring

private theorem diagonal_score {k m r : ℕ} (d : Fin k → ℝ) (Z : Block k r) (Y : Block m r)
    (w : ℕ → Fin r → ℝ) (hw : ∀ j, moment d j Z Y = diagonal (fun i => ((w j i : ℝ) : ℂ)))
    (hn : ∀ i, w 10 i ≠ 0) : powerScore 1 5 d Z Y = ∑ i, (w 2 i - (w 10 i)⁻¹ * (w 6 i)^2) := by
  have hi : (diagonal (fun i => ((w 10 i : ℝ) : ℂ)))⁻¹ =
      diagonal (fun i => ((((w 10 i)⁻¹ : ℝ)) : ℂ)) := by
    apply inv_eq_right_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp [hn]
  change ((moment d 2 Z Y).trace - ((moment d 10 Z Y)⁻¹ * (moment d 6 Z Y)^2).trace).re = _
  rw [hw,hw,hw,hi,sq,diagonal_mul_diagonal,diagonal_mul_diagonal]
  simp [Finset.sum_sub_distrib, ← Complex.ofReal_mul, ← Complex.ofReal_sum, sq]

private theorem frame_of_zero {k m r : ℕ} (d : Fin k → ℝ) (Z : Block k r) (Y : Block m r)
    (h : moment d 0 Z Y = 1) : frame Z Y := by simpa [frame,moment] using h

private theorem moment_entries {k m r : ℕ} (d : Fin k → ℝ) (j : ℕ) (Z : Block k r)
    (Y : Block m r) (u v : Fin r) :
    moment d j Z Y u v = (∑ i, star (Z i u) * ((d i ^ j : ℝ) : ℂ) * Z i v) +
      ∑ i, star (Y i u) * Y i v := by
  unfold moment
  rw [Matrix.add_apply,Matrix.mul_apply,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]

private theorem single_attains (b c : ℝ) (hb : 0<b) (hc : 0<c) :
    pairWeight b c ∈ scores 2 1 5 ![b,c] := by
  let Z : Block 2 1 := ![fun _ => coeff b c, fun _ => coeff c b]
  let Y : Block 2 1 := 0
  have hw (j : ℕ) : moment ![b,c] j Z Y = diagonal (fun _ => ((lineMoment b c j : ℝ) : ℂ)) := by
    ext i l
    rw [moment_entries]
    fin_cases i; fin_cases l
    have conjugate (x y : ℝ) : (starRingEnd ℂ) (coeff x y) = coeff x y := star_coeff x y
    simpa [Z,Y,conjugate,Fin.sum_univ_two] using line_calc hb hc j
  refine ⟨1,Z,Y,frame_of_zero ![b,c] Z Y ?_,?_⟩
  · rw [hw, line_zero hb hc]; simp
  · rw [diagonal_score _ _ _ _ hw (fun _ => by rw [line_ten hb hc]; positivity)]
    simp [line_value hb hc]

private theorem double_attains (d : Fin 2 → ℝ) (hd : ∀ i, 0<d i) :
    (∑ i, pairWeight (d i) 1) ∈ scores 2 1 5 d := by
  let Z : Block 2 2 := diagonal fun i => coeff (d i) 1
  let Y : Block 2 2 := diagonal fun i => coeff 1 (d i)
  have hw (j : ℕ) : moment d j Z Y = diagonal (fun i => ((lineMoment (d i) 1 j : ℝ) : ℂ)) := by
    simp only [moment,Z,Y,diagonal_conjTranspose,diagonal_mul_diagonal,diagonal_add]
    apply congrArg (fun f : Fin 2 → ℂ => diagonal f)
    funext i
    simpa [star_coeff] using line_calc (hd i) zero_lt_one j
  refine ⟨2,Z,Y,frame_of_zero d Z Y ?_,?_⟩
  · rw [hw]
    simp [line_zero (hd _) zero_lt_one]
  · rw [diagonal_score _ _ _ _ hw (fun i => by rw [line_ten (hd i) zero_lt_one]; exact mul_ne_zero (pow_ne_zero _ (hd i).ne') (by norm_num))]
    simp [line_value (hd _) zero_lt_one]

theorem two_exception_maximum (n : ℕ) (b c : ℝ) (hb : 0<b) (hc : 0<c) :
    IsGreatest (scores (2+n) 1 5 ![b,c]) (bestTwo b c) := by
  have hd : ∀ i : Fin 2, 0 < (![b,c] : Fin 2 → ℝ) i := by intro i; fin_cases i <;> assumption
  rw [saturation n 1 5 _ hd]
  refine ⟨?_,?_⟩
  · rcases le_total (pairWeight b c) (pairWeight b 1 + pairWeight c 1) with h|h
    · rw [bestTwo,max_eq_right h]
      simpa [Fin.sum_univ_two] using double_attains ![b,c] hd
    · rw [bestTwo,max_eq_left h]
      exact single_attains b c hb hc
  · rintro _ ⟨r,Z,Y,h,rfl⟩
    exact two_upper b c hb hc Z Y h

/-- Normalized probability set when b and c are measured in units of the background. -/
def probabilities (m : ℕ) (b c : ℝ) : Set ℝ :=
  (fun s => s / (b^2+c^2+m)) '' scores m 1 5 ![b,c]

theorem normalized_maximum (n : ℕ) (b c : ℝ) (hb : 0<b) (hc : 0<c) :
    IsGreatest (probabilities (2+n) b c) (bestTwo b c / (b^2+c^2+(2+n : ℕ))) := by
  obtain ⟨attains,upper⟩ := two_exception_maximum n b c hb hc
  refine ⟨⟨_,attains,rfl⟩,?_⟩
  rintro _ ⟨s,hs,rfl⟩
  exact div_le_div_of_nonneg_right (upper hs) (by positivity)

theorem plastic_dilution (n : ℕ) {ρ b c : ℝ} (hρ : ρ^3=ρ+1) (hb : 0<b) (hc : 0<c) :
    ∀ s ∈ probabilities (2+n) b c,
      s ≤ ((8*ρ^2+ρ-11)/25) * ((b^2+c^2+2)/(b^2+c^2+(2+n : ℕ))) := by
  have h4 : ∀ i : Fin 4, 0 < (![b,c,1,1] : Fin 4 → ℝ) i := by
    intro i; fin_cases i <;> first | assumption | exact zero_lt_one
  have ub : bestTwo b c ≤ ((8*ρ^2+ρ-11)/25) * (b^2+c^2+2) := by
    simpa [bestTwo,pairWeight,HardyFourPairing.matchingMax,HardyTripleGap.edge,
      Fin.sum_univ_four,add_assoc,one_add_one_eq_two] using HardyFourPairing.matchingMax_le_plastic hρ _ h4
  intro s hs
  rw [← mul_div_assoc]
  exact ((normalized_maximum n b c hb hc).2 hs).trans (div_le_div_of_nonneg_right ub (by positivity))

end
end HardyCompression

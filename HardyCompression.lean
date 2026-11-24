module
public import Mathlib

@[expose] public section
namespace HardyCompression
open Matrix
open scoped ComplexOrder MatrixOrder
noncomputable section
variable {k m r : ℕ}
abbrev Block (i j : ℕ) := Matrix (Fin i) (Fin j) ℂ

/-- Both row blocks describe one orthonormal terminal frame. -/
def frame (Z : Block k r) (Y : Block m r) : Prop :=
  Zᴴ * Z + Yᴴ * Y = 1

/-- Compressed power for exceptional amplitudes d and background amplitude one. -/
def moment (d : Fin k → ℝ) (j : ℕ) (Z : Block k r) (Y : Block m r) : Block r r :=
  Zᴴ * diagonal (fun i => ((d i ^ j : ℝ) : ℂ)) * Z + Yᴴ * Y

/-- Schur-complement score for powers p and q. The two-step Hardy case is (1,5). -/
def powerScore (p q : ℕ) (d : Fin k → ℝ) (Z : Block k r) (Y : Block m r) : ℝ :=
  let A := moment d (2*p) Z Y
  let B := moment d (p+q) Z Y
  let C := moment d (2*q) Z Y
  (A.trace - (C⁻¹ * B^2).trace).re

private def shift (Z : Block k r) (L : Block k k) : Block r r := 1 + Zᴴ * L * Z

private theorem shifted_moment (Z : Block k r) (Y : Block m r) (h : frame Z Y)
    (d : Fin k → ℝ) (j : ℕ) :
    moment d j Z Y = shift Z (diagonal (fun i => ((d i ^ j : ℝ) : ℂ)) - 1) := by
  unfold frame at h
  have hy : Yᴴ * Y = 1 - Zᴴ * Z := by rw [← h]; abel
  simp [hy, moment, shift, Matrix.mul_sub, Matrix.sub_mul]
  abel

private theorem moment_unit (Z : Block k r) (Y : Block m r) (h : frame Z Y)
    (d : Fin k → ℝ) (hd : ∀ i, 0 < d i) (j : ℕ) : IsUnit (moment d j Z Y).det := by
  let X := fromRows Z Y
  have hX : Xᴴ * X = 1 := by simpa [frame, X, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows] using h
  have inj : Function.Injective X.mulVec :=
    Function.LeftInverse.injective (g := Xᴴ.mulVec) (fun v => by simp [mulVec_mulVec,hX])
  let D : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ :=
    fromBlocks (diagonal (fun i => ((d i ^ j : ℝ) : ℂ))) 0 0 1
  have hD : D.PosDef := by
    have he : D = diagonal (Sum.elim (fun i => ((d i ^ j : ℝ) : ℂ)) (fun _ => 1)) := by
      ext i l
      rcases i with i|i <;> rcases l with l|l <;> simp [D, fromBlocks, diagonal, one_apply]
    rw [he]
    apply PosDef.diagonal
    rintro (i|i)
    · change (0 : ℂ) < ((d i ^ j : ℝ) : ℂ)
      exact_mod_cast pow_pos (hd i) j
    · exact zero_lt_one
  have he : Xᴴ * D * X = moment d j Z Y := by
    simp [Matrix.mul_assoc,X,D,conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromBlocks_mul_fromRows,fromCols_mul_fromRows,moment]
  exact (isUnit_iff_isUnit_det _).mp (he ▸ (hD.conjTranspose_mul_mul_same inj)).isUnit

/-- A rectangular inverse contraction depends only on the exceptional Gram matrix. -/
private theorem kernel_formula (Z : Block k r) (L : Block k k)
    (h : IsUnit (shift Z L).det) :
    Z * (shift Z L)⁻¹ * Zᴴ = (1 + Z * Zᴴ * L)⁻¹ * (Z * Zᴴ) := by
  let Q := 1 + Z * Zᴴ * L
  let S := shift Z L
  have hQ : IsUnit Q.det := by
    simpa [Q,S,shift,Matrix.mul_assoc,det_one_add_mul_comm Z (Zᴴ * L)] using h
  have inter : Q * Z = Z * S := by
    simp [Q,S,shift,Matrix.add_mul,Matrix.mul_add,Matrix.mul_assoc]
  have left : Q⁻¹ * (Q * Z * S⁻¹) = Z * S⁻¹ := by
    simp only [← Matrix.mul_assoc,nonsing_inv_mul Q hQ, Matrix.one_mul]
  rw [inter, Matrix.mul_assoc, mul_nonsing_inv S h, Matrix.mul_one] at left
  change Z * S⁻¹ * Zᴴ = Q⁻¹ * (Z * Zᴴ)
  rw [← left,Matrix.mul_assoc]

private theorem short_trace (Z : Block k r) (A B C : Block k k)
    (hc : IsUnit (shift Z C).det) :
    (shift Z A).trace - ((shift Z C)⁻¹ * (shift Z B)^2).trace =
    ((A - B - B + C) * (Z * Zᴴ)).trace -
      ((B-C) * ((1 + Z * Zᴴ * C)⁻¹ * (Z * Zᴴ)) * (B-C) * (Z * Zᴴ)).trace := by
  let S := shift Z C
  let M := shift Z B
  let N := shift Z A
  let E := M-S
  have si := mul_nonsing_inv S hc
  have is' := nonsing_inv_mul S hc
  have sub : N - M*S⁻¹*M = (N-M-M+S) - E*S⁻¹*E := by
    simp only [E, Matrix.sub_mul, Matrix.mul_sub, si, Matrix.one_mul,
      Matrix.mul_assoc, is', Matrix.mul_one]
    abel
  have first : N-M-M+S = Zᴴ * (A-B-B+C) * Z := by
    simp [N,M,S,shift,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul]
    abel
  have second : E = Zᴴ * (B-C) * Z := by
    simp [E,M,S,shift, Matrix.mul_sub,Matrix.sub_mul]
  change N.trace - (S⁻¹ * M^2).trace = _
  rw [sq, ← Matrix.mul_assoc, Matrix.trace_mul_comm (S⁻¹ * M) M, ← Matrix.mul_assoc,
    ← Matrix.trace_sub, sub, Matrix.trace_sub,first,second, ← kernel_formula Z C hc]
  congr 1
  · rw [Matrix.mul_assoc, Matrix.trace_mul_comm Zᴴ, Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Zᴴ]
    simp only [Matrix.mul_assoc, S]

private theorem complement_positive (Z : Block k r) (Y : Block m r) (h : frame Z Y) :
    (1-Z*Zᴴ).PosSemidef := by
  let P := Z*Zᴴ
  have hy : Yᴴ * Y = 1-Zᴴ*Z := by
    unfold frame at h
    rw [← h]; abel
  have hp : Pᴴ = P := by simp [P]
  have he : (1-P)ᴴ * (1-P) + (Y*Zᴴ)ᴴ * (Y*Zᴴ) = 1-P := by
    simp only [conjTranspose_sub,conjTranspose_one,hp,conjTranspose_mul,conjTranspose_conjTranspose]
    rw [← Matrix.mul_assoc (Z * Yᴴ), Matrix.mul_assoc Z Yᴴ Y, hy]
    simp [P, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [← he]
  exact (posSemidef_conjTranspose_mul_self _).add (posSemidef_conjTranspose_mul_self _)

theorem compress_frame (Z : Block k r) (Y : Block m r) (h : frame Z Y) :
    ∃ U V : Block k k, frame U V ∧ U*Uᴴ = Z*Zᴴ ∧
      ∀ (p q : ℕ) (d : Fin k → ℝ), (∀ i, 0 < d i) → powerScore p q d U V = powerScore p q d Z Y := by
  let P := Z*Zᴴ
  let U := CFC.sqrt P
  let V := CFC.sqrt (1-P)
  have hp : 0 ≤ P := (posSemidef_self_mul_conjTranspose _).nonneg
  have hv : 0 ≤ 1-P := (complement_positive Z Y h).nonneg
  have hu1 : Uᴴ = U := (CFC.sqrt_nonneg P).posSemidef.isHermitian
  have hv1 : Vᴴ = V := (CFC.sqrt_nonneg (1-P)).posSemidef.isHermitian
  have hu2 : U*U = P := by simpa [U,sq] using CFC.sq_sqrt P hp
  have hv2 : V*V = 1-P := by simpa [V,sq] using CFC.sq_sqrt (1-P) hv
  have hUV : frame U V := by unfold frame; rw [hu1,hv1,hu2,hv2]; abel
  have same : U*Uᴴ = Z*Zᴴ := by rw [hu1,hu2]
  refine ⟨U,V,hUV,same,fun p q d hd => ?_⟩
  have hz := moment_unit Z Y h d hd (2*q)
  have hu := moment_unit U V hUV d hd (2*q)
  rw [shifted_moment _ _ h] at hz
  rw [shifted_moment _ _ hUV] at hu
  simp only [powerScore, shifted_moment _ _ h, shifted_moment _ _ hUV, short_trace _ _ _ _ hu,
    short_trace _ _ _ _ hz, same]
/-- All scores, with endpoint rank free. -/
def scores (m p q : ℕ) (d : Fin k → ℝ) : Set ℝ :=
  {s | ∃ r, ∃ Z : Block k r, ∃ Y : Block m r, frame Z Y ∧ s = powerScore p q d Z Y}

private def pad (n : ℕ) (Y : Block m r) : Block (m+n) r :=
  fun i j => if h : i.val < m then Y ⟨i.val,h⟩ j else 0

private theorem pad_gram (n : ℕ) (Y : Block m r) : (pad n Y)ᴴ * pad n Y = Yᴴ * Y := by
  ext i j
  rw [Matrix.mul_apply,Matrix.mul_apply,Fin.sum_univ_add]
  simp only [Matrix.conjTranspose_apply]
  simp [pad]

theorem saturation (n p q : ℕ) (d : Fin k → ℝ) (hd : ∀ i, 0 < d i) :
    scores (k+n) p q d = scores k p q d := by
  ext s
  constructor
  · rintro ⟨r,Z,Y,h,rfl⟩
    obtain ⟨U,V,hu,_,he⟩ := compress_frame Z Y h
    exact ⟨k,U,V,hu,(he p q d hd).symm⟩
  · rintro ⟨r,Z,Y,h,rfl⟩
    exact ⟨r,Z,pad n Y,by simpa [frame,pad_gram] using h,by simp [powerScore,moment,pad_gram]⟩

end
end HardyCompression

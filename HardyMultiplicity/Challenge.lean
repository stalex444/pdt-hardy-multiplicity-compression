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

/-- All scores, with endpoint rank free. -/
def scores (m p q : ℕ) (d : Fin k → ℝ) : Set ℝ :=
  {s | ∃ r, ∃ Z : Block k r, ∃ Y : Block m r, frame Z Y ∧ s = powerScore p q d Z Y}

def pairWeight (x y : ℝ) : ℝ := ((x*y^5-y*x^5)/(x^5+y^5))^2

def bestTwo (b c : ℝ) : ℝ := max (pairWeight b c) (pairWeight b 1 + pairWeight c 1)

/-- Normalized probability set when b and c are measured in units of the background. -/
def probabilities (m : ℕ) (b c : ℝ) : Set ℝ :=
  (fun s => s / (b^2+c^2+m)) '' scores m 1 5 ![b,c]

theorem frame_compression {k m r : ℕ} (Z : Block k r) (Y : Block m r) (h : frame Z Y) :
    ∃ U V : Block k k, frame U V ∧ U*Uᴴ = Z*Zᴴ ∧
      ∀ (p q : ℕ) (d : Fin k → ℝ), (∀ i, 0 < d i) → powerScore p q d U V = powerScore p q d Z Y := by sorry

theorem score_set_stabilization {k : ℕ} (n p q : ℕ) (d : Fin k → ℝ) (hd : ∀ i, 0 < d i) :
    scores (k+n) p q d = scores k p q d := by sorry

theorem sharp_repeated_spectrum (n : ℕ) (b c : ℝ) (hb : 0<b) (hc : 0<c) :
    IsGreatest (probabilities (2+n) b c) (bestTwo b c / (b^2+c^2+(2+n : ℕ))) := by sorry

theorem multiplicity_penalty (n : ℕ) {ρ b c : ℝ} (hρ : ρ^3=ρ+1) (hb : 0<b) (hc : 0<c) :
    ∀ s ∈ probabilities (2+n) b c,
      s ≤ ((8*ρ^2+ρ-11)/25) * ((b^2+c^2+2)/(b^2+c^2+(2+n : ℕ))) := by sorry

end
end HardyCompression

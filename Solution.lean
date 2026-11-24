module
public import HardySharp

@[expose] public section
namespace HardyCompression
open Matrix
noncomputable section

theorem frame_compression {k m r : ℕ} (Z : Block k r) (Y : Block m r) (h : frame Z Y) :
    ∃ U V : Block k k, frame U V ∧ U*Uᴴ = Z*Zᴴ ∧
      ∀ (p q : ℕ) (d : Fin k → ℝ), (∀ i, 0 < d i) → powerScore p q d U V = powerScore p q d Z Y :=
  compress_frame Z Y h

theorem score_set_stabilization {k : ℕ} (n p q : ℕ) (d : Fin k → ℝ) (hd : ∀ i, 0 < d i) :
    scores (k+n) p q d = scores k p q d :=
  saturation n p q d hd

theorem sharp_repeated_spectrum (n : ℕ) (b c : ℝ) (hb : 0<b) (hc : 0<c) :
    IsGreatest (probabilities (2+n) b c) (bestTwo b c / (b^2+c^2+(2+n : ℕ))) :=
  normalized_maximum n b c hb hc

theorem multiplicity_penalty (n : ℕ) {ρ b c : ℝ} (hρ : ρ^3=ρ+1) (hb : 0<b) (hc : 0<c) :
    ∀ s ∈ probabilities (2+n) b c,
      s ≤ ((8*ρ^2+ρ-11)/25) * ((b^2+c^2+2)/(b^2+c^2+(2+n : ℕ))) :=
  plastic_dilution n hρ hb hc

end
end HardyCompression

#print axioms HardyCompression.frame_compression
#print axioms HardyCompression.score_set_stabilization
#print axioms HardyCompression.sharp_repeated_spectrum
#print axioms HardyCompression.multiplicity_penalty

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Resampling one coordinate independently

Product-almost-everywhere tests remain true after one coordinate is
independently resampled from an absolutely continuous probability law
(`ae_update_pi`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.IndependentCoordinateResampling

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- Product-almost-everywhere tests remain true after independently
resampling one coordinate from an actual absolutely continuous probability
law. No arbitrary joint parent density is assumed. -/
theorem ae_update_pi (σ : Measure Ω) [IsProbabilityMeasure σ] (hσ : σ ≪ ν)
    {n : ℕ} (i : Fin (n + 1)) (P : (Fin (n + 1) → Ω) → Prop)
    (hP : ∀ᵐ v ∂Measure.pi (fun _ : Fin (n + 1) => ν), P v) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin (n + 1) => ν),
      ∀ᵐ z ∂σ, P (Function.update v i z) := by
  let ρ := Measure.pi (fun _ : Fin (n + 1) => ν)
  let τ := Measure.pi (fun _ : Fin n => ν)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) i
  have he : MeasurePreserving e ρ (ν.prod τ) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i
  have hback : MeasurePreserving e.symm (ν.prod τ) ρ := MeasurePreserving.symm e he
  have hgood : ∀ᵐ p ∂σ.prod τ, P (e.symm p) :=
    (hσ.prod Measure.AbsolutelyContinuous.rfl).ae_le (hback.quasiMeasurePreserving.ae hP)
  have htail : MeasurePreserving (Fin.removeNth i) ρ τ :=
    (measurePreserving_snd (μ := ν) (ν := τ)).comp he
  have hid : MeasurePreserving (id : Ω → Ω) σ σ := ⟨measurable_id, Measure.map_id⟩
  have hjoint := (hid.prod htail).quasiMeasurePreserving.ae hgood
  have hupdate (z : Ω) (v : Fin (n + 1) → Ω) :
      e.symm (z, Fin.removeNth i v) = Function.update v i z := by
    change Fin.insertNth i z (Fin.removeNth i v) = _
    exact Fin.insertNth_removeNth i z v
  have hroot : ∀ᵐ p ∂σ.prod ρ, P (Function.update p.2 i p.1) :=
    hjoint.mono (fun p hp => by
      change P (e.symm (p.1, Fin.removeNth i p.2)) at hp
      rwa [hupdate] at hp)
  have hswap := (Measure.measurePreserving_swap (μ := ρ) (ν := σ)).quasiMeasurePreserving.ae hroot
  exact Measure.ae_ae_of_ae_prod hswap

end Erdos1017.IndependentCoordinateResampling

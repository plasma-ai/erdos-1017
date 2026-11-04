module

public import Erdos1017.Models.Decorated.DecoratedKernel

/-!
# Extensionality of decorated kernels

Pointwise equality of the conditional color laws determines the entire decorated
kernel, including its proof-valued fields (`ext_kernel`).
-/

@[expose] public section

namespace Erdos1017.DecoratedKernel

open MeasureTheory ProbabilityTheory

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {μ : Measure Ω}

/-- Pointwise equality of the actual conditional color laws determines the
entire decorated kernel, including its proof-valued fields. -/
theorem ext_kernel (W V : DecoratedKernel Ω C μ)
    (h : ∀ p, W.kernel p = V.kernel p) : W = V := by
  have hkernel : W.kernel = V.kernel := Kernel.ext h
  cases W
  cases V
  cases hkernel
  rfl

end Erdos1017.DecoratedKernel

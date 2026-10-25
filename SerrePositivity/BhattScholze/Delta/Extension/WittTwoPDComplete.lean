module

public import SerrePositivity.BhattScholze.Delta.Extension.WittTwoModuleComplete
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaFrobeniusComplete

/-! # p,d導来完備な終域へのW₂のδ基底作用

P2の接続。終域のφ(d)完備性はδ公式と既存の漸化式判定から証明して供給する。
古典的完備性、p正則性、ねじれの有界性を追加しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- p,f(d)実導来完備な終域に対し、W₂はδ基底作用についてd実導来完備。 -/
theorem wittTwo_isModuleComplete_d (D : DeltaStructure p A) (f : A →+* B) (d : A)
    (hp : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hd : IsModuleComplete B (f d) (ModuleCat.of B B)) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    IsModuleComplete A d (ModuleCat.of A (WittTwo p B)) :=
  wittTwo_isModuleComplete D f d hd (deltaImage_frobenius_isModuleComplete D f d hp hd)

end SerrePositivity.BhattScholze

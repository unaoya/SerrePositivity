module

public import SerrePositivity.KST.Spectra.WeightCylinderLifting

/-!
概要：重みの cylinder は重みの射に関して関手的。
方針：自然変換の各成分に右 tensor を施し、二端の自然性を厳密に計算する。
規約：ホモトピーの向きを反転しない。
使われ方：Goerss–Jardine VII §4。二射影の垂直ホモトピーから比較逆を組み立てる。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.WeightCylinderFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 重みの射を cylinder の第一因子へ tensor した自然変換。 -/
def map {F G : CosimplicialObject SSet.{u}} (f : F ⟶ G) (A : SSet.{u}) :
    WeightTensorLatching.diagram F A ⟶ WeightTensorLatching.diagram G A where
  app j := f.app j ▷ A
  naturality i j h := by
    change (F.map h ▷ A) ≫ (f.app j ▷ A) = (f.app i ▷ A) ≫ (G.map h ▷ A)
    rw [← comp_whiskerRight, ← comp_whiskerRight, f.naturality h]

/-- cylinder の零端は第一因子の射に自然。 -/
@[reassoc]
lemma zero_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.ι₀ ≫ (f ▷ (Δ[1] : SSet.{u})) = f ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- cylinder の一端も第一因子の射に自然。 -/
@[reassoc]
lemma one_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.ι₁ ≫ (f ▷ (Δ[1] : SSet.{u})) = f ≫ SSet.ι₁ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- cylinder の零端の計算は重みの前合成と係数の後合成で保たれる。 -/
lemma zero_composite {F G X Y : CosimplicialObject SSet.{u}}
    (a : F ⟶ G) (H : WeightTensorLatching.diagram G (Δ[1] : SSet.{u}) ⟶ X)
    (b : X ⟶ Y) (f : G ⟶ X) (h : ∀ j, SSet.ι₀ ≫ H.app j = f.app j) (j : SimplexCategory) :
    SSet.ι₀ ≫ (map a (Δ[1] : SSet.{u}) ≫ H ≫ b).app j = (a ≫ f ≫ b).app j := by
  change SSet.ι₀ ≫ ((a.app j ▷ (Δ[1] : SSet.{u})) ≫ H.app j ≫ b.app j) =
    a.app j ≫ f.app j ≫ b.app j
  rw [zero_naturality_assoc]
  simpa only [Category.assoc] using congrArg (fun t ↦ a.app j ≫ t ≫ b.app j) (h j)

/-- cylinder の一端の計算も前合成と後合成で保たれる。 -/
lemma one_composite {F G X Y : CosimplicialObject SSet.{u}}
    (a : F ⟶ G) (H : WeightTensorLatching.diagram G (Δ[1] : SSet.{u}) ⟶ X)
    (b : X ⟶ Y) (f : G ⟶ X) (h : ∀ j, SSet.ι₁ ≫ H.app j = f.app j) (j : SimplexCategory) :
    SSet.ι₁ ≫ (map a (Δ[1] : SSet.{u}) ≫ H ≫ b).app j = (a ≫ f ≫ b).app j := by
  change SSet.ι₁ ≫ ((a.app j ▷ (Δ[1] : SSet.{u})) ≫ H.app j ≫ b.app j) =
    a.app j ≫ f.app j ≫ b.app j
  rw [one_naturality_assoc]
  simpa only [Category.assoc] using congrArg (fun t ↦ a.app j ≫ t ≫ b.app j) (h j)

end SerrePositivity.KST.Spectra.WeightCylinderFunctor

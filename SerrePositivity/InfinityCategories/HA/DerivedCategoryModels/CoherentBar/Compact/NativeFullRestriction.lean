module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment
public import SerrePositivity.KST.SConstruction.DGStandardCoherentMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan

/-!
概要：充満 dg 部分圏への制限を、全 Hom end に作用する厳密 dg 関手にする。
方針：任意複体パラメータの元の全成分を制限し、評価で単位・合成を照合する。
規約：閉零変換や通常射だけへ切り詰めない。元のパラメータ複体を保持する。
使われ方：D-4b の実安定核に対する全 native Hom 作用。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory MonoidalCategory DifferentialGraded KST.SConstruction

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (S : C → Prop) (T : D → Prop)

/-- 指定された対象条件を保つ元の dg 関手の充満 dg 部分圏。 -/
abbrev DGFullPreservingFunctor :=
  DGFullSubcategory (DGFunctor R C D) (fun F => ∀ x, S x → T (F.obj x))

/-- 全次数の変換を、両端の同じ制限関手間へ成分を変えずに送る。 -/
def dgFullRestrictionParameter
    (F G : DGFullPreservingFunctor R C D S T) {K : Complex R}
    (τ : DGFunctorParamTrans R C D K F.val G.val) :
    DGFunctorParamTrans R (DGFullSubcategory C S) (DGFullSubcategory D T) K
      (F.val.restrict S T F.property) (G.val.restrict S T G.property) where
  app x := τ.app x.val
  naturality x y := τ.naturality x.val y.val

/-- Hom end の全次数鎖写像。各対象の評価は元の評価そのもの。 -/
def dgFullRestrictionHom (F G : DGFullPreservingFunctor R C D S T) :
    dgFunctorHom R C D F.val G.val ⟶
      dgFunctorHom R (DGFullSubcategory C S) (DGFullSubcategory D T)
        (F.val.restrict S T F.property) (G.val.restrict S T G.property) :=
  (dgFunctorHomEquiv R _ _ _ _ _).symm
    (dgFullRestrictionParameter R C D S T F G
      (dgFunctorHomEquiv R C D _ F.val G.val (𝟙 _)))

@[reassoc (attr := simp)]
lemma dgFullRestrictionHom_π (F G : DGFullPreservingFunctor R C D S T)
    (x : DGFullSubcategory C S) :
    dgFullRestrictionHom R C D S T F G ≫
        dgFunctorHomπ R _ _ _ _ x = dgFunctorHomπ R C D F.val G.val x.val := by
  rw [dgFullRestrictionHom, dgFunctorHomEquiv_symm_π]
  exact Category.id_comp _

lemma dgFullRestrictionHom_identity (F : DGFullPreservingFunctor R C D S T) :
    dgFunctorIdentity R C D F.val ≫ dgFullRestrictionHom R C D S T F F =
      dgFunctorIdentity R _ _ (F.val.restrict S T F.property) := by
  apply dgFunctorHom_ext
  intro x
  rw [Category.assoc, dgFullRestrictionHom_π, dgFunctorIdentity_π,
    dgFunctorIdentity_π]
  rfl

lemma dgFullRestrictionHom_composition (F G H : DGFullPreservingFunctor R C D S T) :
    dgFunctorComposition R C D F.val G.val H.val ≫
        dgFullRestrictionHom R C D S T F H =
      (dgFullRestrictionHom R C D S T F G ⊗ₘ dgFullRestrictionHom R C D S T G H) ≫
        dgFunctorComposition R _ _ (F.val.restrict S T F.property)
          (G.val.restrict S T G.property) (H.val.restrict S T H.property) := by
  apply dgFunctorHom_ext
  intro x
  simp only [Category.assoc, dgFullRestrictionHom_π, dgFunctorComposition_π,
    tensorHom_comp_tensorHom_assoc]
  rfl

/-- 制限の全 Hom 作用を束ねた厳密 dg 関手。 -/
def dgFullRestrictionFunctor :
    DGFunctor R (DGFullPreservingFunctor R C D S T)
      (DGFunctor R (DGFullSubcategory C S) (DGFullSubcategory D T)) where
  obj F := F.val.restrict S T F.property
  map := dgFullRestrictionHom R C D S T
  map_id := dgFullRestrictionHom_identity R C D S T
  map_comp := dgFullRestrictionHom_composition R C D S T

/-- 元の core 上の全単体を保った、充満部分圏への制限の native 作用。 -/
def dgFullRestrictionNativeMap :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R)
      (D := DGFullPreservingFunctor R C D S T)) : SSet) ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R)
      (D := DGFunctor R (DGFullSubcategory C S) (DGFullSubcategory D T))) : SSet) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (dgStandardCoherentMap (dgFullRestrictionFunctor R C D S T))

/-- core への制限前後で、元の全単体の標準 coherent nerve 作用を回収する。 -/
lemma dgFullRestrictionNativeMap_inclusion :
    dgFullRestrictionNativeMap R C D S T ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore _).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore _).ι ≫
        dgStandardCoherentMap (dgFullRestrictionFunctor R C D S T) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

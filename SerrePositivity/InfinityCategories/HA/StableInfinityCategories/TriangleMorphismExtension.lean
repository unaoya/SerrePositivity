module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquareHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Triangulated

/-! # Cofiber 三角形の射の延長

概要：最初の二成分の可換正方形を cofiber 三角形の射へ延長する。
方針：二成分を辺で表して四角形間のホモトピーへ持ち上げ、既存の三角形の射を適用する。
規約：前加法構造や Pretriangulated instance を仮定しない。
使われ方：S4 の TR3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber 三角形の最初の二成分の可換正方形は三角形の射へ延長できる。
方針：二成分を辺で表し、cofiber 図式間のホモトピーを構成して成分を照合する。
規約：指定した二成分は厳密に保持する。使われ方：TR3 の代表上での証明。 -/
lemma exists_cofiberTriangleMorphism_of_comm {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence d)
    (u : t.hoShortComplex.X₁ ⟶ d.hoShortComplex.X₁)
    (v : t.hoShortComplex.X₂ ⟶ d.hoShortComplex.X₂)
    (h : t.hoShortComplex.f ≫ v = u ≫ d.hoShortComplex.f) :
    ∃ m : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d hd, m.hom₁ = u ∧ m.hom₂ = v := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 0) u
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 1 0) v
  have hc : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom t.square ≫ SSet.Truncated.HomotopyCategory.homMk b =
      SSet.Truncated.HomotopyCategory.homMk a ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom d.square := by
    rw [ha, hb]
    exact h
  obtain ⟨Q, hQ₀, hQ₁⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_cofiberSquareHomotopy_of_comm t d ht hd a b hc
  let m := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleMapOfHomotopy t d ht hd Q
  have hi (j : Fin 2) : SSet.yonedaEquiv
      (stdSimplex.δ j.rev ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) j 0 := by
    fin_cases j <;> apply Prod.ext <;> decide
  refine ⟨m, ?_, ?_⟩
  · apply Arrow.mk_injective
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints_vertexPath_arrow Q
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) a hQ₀
    have hi₀ := hi 0
    change SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) = _ at hi₀
    rw [hi₀] at hh
    exact hh.trans (congrArg Arrow.mk ha)
  · apply Arrow.mk_injective
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints_vertexPath_arrow Q
      (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) b hQ₁
    have hi₁ := hi 1
    change SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) = _ at hi₁
    rw [hi₁] at hh
    exact hh.trans (congrArg Arrow.mk hb)

/-- 概要：cofiber distinguished triangle の間の任意の可換正方形は三角形の射へ延長できる。
方針：cofiber の代表へ同型で移し、代表上で延長した射を元の三角形へ戻す。
規約：最初の二成分は指定されたものに等しい。使われ方：TR3 の一般の三角形上での証明。 -/
lemma exists_cofiberDistinguishedTriangleMorphism {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {T U : Triangle (hoFunctor.obj X)}
    (hT : T ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X) (hU : U ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X)
    (u : T.obj₁ ⟶ U.obj₁) (v : T.obj₂ ⟶ U.obj₂) (h : T.mor₁ ≫ v = u ≫ U.mor₁) :
    ∃ m : T ⟶ U, m.hom₁ = u ∧ m.hom₂ = v := by
  obtain ⟨t, ht, ⟨i⟩⟩ := hT
  obtain ⟨d, hd, ⟨j⟩⟩ := hU
  let u' := i.inv.hom₁ ≫ u ≫ j.hom.hom₁
  let v' := i.inv.hom₂ ≫ v ≫ j.hom.hom₂
  have hc : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).mor₁ ≫ v' = u' ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d hd).mor₁ := by
    dsimp only [u', v']
    calc
      _ = i.inv.hom₁ ≫ T.mor₁ ≫ v ≫ j.hom.hom₂ := by
        simpa only [Category.assoc] using
          congrArg (fun q ↦ q ≫ v ≫ j.hom.hom₂) i.inv.comm₁
      _ = i.inv.hom₁ ≫ u ≫ U.mor₁ ≫ j.hom.hom₂ := by rw [reassoc_of% h]
      _ = _ := by rw [j.hom.comm₁]; simp only [Category.assoc]
  obtain ⟨m, hm₁, hm₂⟩ := exists_cofiberTriangleMorphism_of_comm t d ht hd u' v' hc
  have hi₁ : i.hom.hom₁ ≫ i.inv.hom₁ = 𝟙 _ := congrArg TriangleMorphism.hom₁ i.hom_inv_id
  have hi₂ : i.hom.hom₂ ≫ i.inv.hom₂ = 𝟙 _ := congrArg TriangleMorphism.hom₂ i.hom_inv_id
  have hj₁ : j.hom.hom₁ ≫ j.inv.hom₁ = 𝟙 _ := congrArg TriangleMorphism.hom₁ j.hom_inv_id
  have hj₂ : j.hom.hom₂ ≫ j.inv.hom₂ = 𝟙 _ := congrArg TriangleMorphism.hom₂ j.hom_inv_id
  refine ⟨i.hom ≫ m ≫ j.inv, ?_, ?_⟩
  · change i.hom.hom₁ ≫ m.hom₁ ≫ j.inv.hom₁ = u
    rw [hm₁]
    dsimp only [u']
    simp only [Category.assoc, reassoc_of% hi₁, hj₁, Category.comp_id]
  · change i.hom.hom₂ ≫ m.hom₂ ≫ j.inv.hom₂ = v
    rw [hm₂]
    dsimp only [v']
    simp only [Category.assoc, reassoc_of% hi₂, hj₂, Category.comp_id]

/-- 概要：distinguished な二三角形の可換正方形には第三成分と残りの可換式が存在する。
方針：二成分を保持した三角形の射から第三成分を取る。
規約：Pretriangulated の TR3 と同じ可換式の形。使われ方：将来の instance の公理。 -/
lemma complete_cofiberDistinguishedTriangle_morphism {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {T U : Triangle (hoFunctor.obj X)}
    (hT : T ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X) (hU : U ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X)
    (u : T.obj₁ ⟶ U.obj₁) (v : T.obj₂ ⟶ U.obj₂) (h : T.mor₁ ≫ v = u ≫ U.mor₁) :
    ∃ w : T.obj₃ ⟶ U.obj₃, T.mor₂ ≫ w = v ≫ U.mor₂ ∧
      T.mor₃ ≫ (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map u = w ≫ U.mor₃ := by
  obtain ⟨m, hm₁, hm₂⟩ := exists_cofiberDistinguishedTriangleMorphism hT hU u v h
  refine ⟨m.hom₃, ?_, ?_⟩
  · simpa only [hm₂] using m.comm₂
  · simpa only [hm₁] using m.comm₃

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

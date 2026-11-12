module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingTranspose

/-!
概要：非定値の関手 U,V の間の写像空間の族をホモトピーへ展開する。
方針：射の区間・関手の変数・族のパラメータを入れ替えて curry と uncurry を使う。
規約：端点は fst ≫ U と fst ≫ V。定値関手には制限しない。
使われ方：随伴の各点の写像空間条件と非定値 U,V の対応を結ぶ準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：関手 U,V の間の区間写像空間の族を二重パラメータの区間の射へ展開する。
方針：内部 Hom の評価の変数を区間と交換して uncurry する。
規約：区間は第一因子、A が関手の変数、B が族の変数。
使われ方：非定値の端点を持つ自然変換の族。 -/
def transformationFamilyUncurry {A B X : SSet.{u}} {U V : A ⟶ X}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) :
    (Δ[1] : SSet.{u}) ⊗ (A ⊗ B) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalParameterSwap A B ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)

/-- 概要：展開した族の始点は U のパラメータに定値な延長。
方針：区間交換の端点公式と定値関手頂点の uncurry を使う。
規約：U 自体は定値ではない。
使われ方：族を U から V へのホモトピーとして扱う。 -/
lemma transformationFamilyUncurry_zero {A B X : SSet.{u}} {U V : A ⟶ X}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ B) ≫ transformationFamilyUncurry f = fst A B ≫ U := by
  unfold transformationFamilyUncurry
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalParameterSwap_endpoint, ← uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：展開した族の終点は V のパラメータに定値な延長。
方針：区間交換の端点公式と定値関手頂点の uncurry を使う。
規約：V 自体は定値ではない。
使われ方：族を U から V へのホモトピーとして扱う。 -/
lemma transformationFamilyUncurry_one {A B X : SSet.{u}} {U V : A ⟶ X}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ B) ≫ transformationFamilyUncurry f = fst A B ≫ V := by
  unfold transformationFamilyUncurry
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalParameterSwap_endpoint, ← uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：U,V 間の写像空間の B 族を A×B 上のホモトピーにする。
方針：展開した区間の射を標準の区間が第二因子の向きへ戻す。
規約：B と A と X の quasicategory 性は不要。
使われ方：非定値端点の族と自然変換の往復。 -/
noncomputable def transformationFamilyHomotopy {A B X : SSet.{u}} {U V : A ⟶ X}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) :
    SSet.Homotopy (fst A B ≫ U) (fst A B ≫ V) where
  h := (β_ (A ⊗ B) (Δ[1] : SSet.{u})).hom ≫ transformationFamilyUncurry f
  h₀ := by
    rw [← Category.assoc]
    exact transformationFamilyUncurry_zero f
  h₁ := by
    rw [← Category.assoc]
    exact transformationFamilyUncurry_one f
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：A、区間、B を A×B と区間へ並べ替える。
方針：最後の二因子の交換と結合子の逆を使う。
規約：標準ホモトピーでは時間は第二因子。
使われ方：非定値端点の族への curry の逆向き。 -/
def transformationFamilyReorder (A B : SSet.{u}) :
    A ⊗ ((Δ[1] : SSet.{u}) ⊗ B) ⟶ (A ⊗ B) ⊗ (Δ[1] : SSet.{u}) :=
  (A ◁ (β_ (Δ[1] : SSet.{u}) B).hom) ≫ (α_ A B Δ[1]).inv

/-- 概要：非定値端点のホモトピーを Fun(A,X) の区間族へ戻す。
方針：区間をパラメータ B と交換し、A の変数を curry する。
規約：両端の関手は U,V そのもの。
使われ方：関手間の自然変換の族の厳密な回収。 -/
noncomputable def transformationFamilyCurry {A B X : SSet.{u}} {U V : A ⟶ X}
    (H : SSet.Homotopy (fst A B ≫ U) (fst A B ≫ V)) :
    B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry (curry (transformationFamilyReorder A B ≫ H.h))
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
      have hc : A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ transformationFamilyReorder A B =
          SSet.ι₀ := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro z
        rfl
      rw [← Category.assoc, hc, H.h₀])
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
      have hc : A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ transformationFamilyReorder A B =
          SSet.ι₁ := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro z
        rfl
      rw [← Category.assoc, hc, H.h₁])

/-- 概要：戻した族の区間の展開の公式。
方針：固定端点を持つ区間族の curry の往復を使う。
規約：与えたホモトピー H を変更しない。
使われ方：二つの構成の両逆を計算する。 -/
lemma transformationFamilyCurry_uncurry {A B X : SSet.{u}} {U V : A ⟶ X}
    (H : SSet.Homotopy (fst A B ≫ U) (fst A B ≫ V)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (transformationFamilyCurry H) =
      curry (transformationFamilyReorder A B ≫ H.h) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry _ _ _

/-- 概要：族をホモトピーへ展開して戻すと元の族。
方針：二つの uncurry の単射性と座標交換の往復を使う。
規約：射としての厳密な等式。
使われ方：非定値端点の族の表示の単射性。 -/
lemma transformationFamilyCurry_homotopy {A B X : SSet.{u}} {U V : A ⟶ X}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) :
    transformationFamilyCurry (transformationFamilyHomotopy f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [transformationFamilyCurry_uncurry]
  apply uncurry_injective
  rw [uncurry_curry]
  simp only [transformationFamilyHomotopy, transformationFamilyUncurry]
  have hc : transformationFamilyReorder A B ≫
      (β_ (A ⊗ B) (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalParameterSwap A B = 𝟙 _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (· ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)) hc

/-- 概要：ホモトピーを族へ戻して展開すると元のホモトピー。
方針：curry の往復と座標交換の反対の往復を使う。
規約：空の相対条件の証明は proof irrelevance で一致する。
使われ方：非定値端点の族の表示の全射性。 -/
lemma transformationFamilyHomotopy_curry {A B X : SSet.{u}} {U V : A ⟶ X}
    (H : SSet.Homotopy (fst A B ≫ U) (fst A B ≫ V)) :
    transformationFamilyHomotopy (transformationFamilyCurry H) = H := by
  apply SSet.RelativeMorphism.Homotopy.ext
  change (β_ (A ⊗ B) (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalParameterSwap A B ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (transformationFamilyCurry H)) = H.h
  rw [transformationFamilyCurry_uncurry, uncurry_curry]
  have hc : (β_ (A ⊗ B) (Δ[1] : SSet.{u})).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalParameterSwap A B ≫ transformationFamilyReorder A B = 𝟙 _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  simpa only [Category.assoc, Category.id_comp] using congrArg (· ≫ H.h) hc

/-- 概要：関手間の写像空間の B 族と A×B 上の非定値端点のホモトピーの全単射。
方針：展開と回収の両逆をまとめる。
規約：ホモトピー類を取る前の厳密な全単射。
使われ方：非定値 U,V を含む写像空間条件への橋。 -/
noncomputable def transformationFamilyEquiv (A B X : SSet.{u}) (U V : A ⟶ X) :
    (B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) ≃
      SSet.Homotopy (fst A B ≫ U) (fst A B ≫ V) where
  toFun := transformationFamilyHomotopy
  invFun := transformationFamilyCurry
  left_inv := transformationFamilyCurry_homotopy
  right_inv := transformationFamilyHomotopy_curry

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

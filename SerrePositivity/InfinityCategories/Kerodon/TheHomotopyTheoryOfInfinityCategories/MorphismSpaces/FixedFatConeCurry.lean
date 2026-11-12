module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedFatConeUniversal

/-!
概要：両端を固定した fat join の図式を固定頂点の錐の空間へ戻す普遍性。
方針：太い slice の curry の普遍族の左端も固定されることを計算し、両端の fiber へ移す。
規約：左端の定値条件と右端の図式の条件を厳密な等式で与える。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の相対 join 延長後の族の回収。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：固定頂点を持つ fat join 図式の curry の普遍族も左端を固定する。
方針：直積と fat join の比較の左端の式を使い、零単体への射の一意性で計算する。
規約：右端の固定条件はこの計算には不要。
使われ方：Kerodon §4.6.6（Tag 04HY） の両端固定の fiber への curry の準備。 -/
lemma fixedFatConeCurryFamily_inl {A K X : SSet.{u}} (x : X _⦋0⦌)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ≫ F = SSet.const x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurryFamily F =
      fst (Δ[0] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm x := by
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ A) ≫
      (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K) A).hom =
      (β_ (Δ[0] : SSet.{u}) A).hom ≫ (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K) := rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurryFamily, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ A), hs]
  simp only [Category.assoc]
  rw [← Category.assoc (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorLeft_inl]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (A ⊗ (Δ[0] : SSet.{u})) K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map]
  simp only [Category.assoc]
  rw [hx, SSet.comp_const, SSet.comp_const]
  have ht : fst (Δ[0] : SSet.{u}) A = SSet.const (stdSimplex.obj₀Equiv.symm 0) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda]

/-- 概要：両端を固定した図式を curry すると、その関手の族は両端の図式に定値。
方針：左右の制限を uncurry して固定条件を使い、直和上の関手の一意性で合わせる。
規約：標的の充填性は仮定しない。
使われ方：Kerodon §4.6.6（Tag 04HY） の固定頂点の錐の空間へ持ち上げる条件。 -/
lemma fixedFatConeCurry_fixed {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ≫ F = SSet.const x)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ F = p) :
    curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurryFamily F) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointFunctor_hom_ext
  · rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_fatInclusion,
      SSet.const_comp]
    change curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurryFamily F) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K)).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x))
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    exact fixedFatConeCurryFamily_inl x F hx
  · rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_fatInclusion,
      SSet.const_comp]
    change curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurryFamily F) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K)).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurryFamily_fixed F hp

/-- 概要：両端を固定した fat join の図式を固定頂点の錐の族へ戻す。
方針：太い slice の普遍族を curry し、両端の固定条件で fiber へ持ち上げる。
規約：パラメータ A は任意である。
使われ方：Kerodon §4.6.6（Tag 04HY） の相対 join 延長から逆射を回収する構成。 -/
noncomputable def fixedFatConeCurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ≫ F = SSet.const x)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ F = p) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurryFamily F)) (fixedFatConeCurry_fixed F hx hp)

/-- 概要：両端固定で curry して頂点の条件を忘れると、既存の太い slice の curry になる。
方針：二つの fiber の持ち上げが同じ族を値とすることを比較する。
規約：充填性なしの射の等式。
使われ方：Kerodon §4.6.6（Tag 04HY） の既存の往復則の移送。 -/
lemma fixedFatConeCurry_toLaxSlice {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ≫ F = SSet.const x)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ F = p) :
    fixedFatConeCurry F hx hp ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeToLaxSlice p x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurry F hp := rfl

/-- 概要：両端固定の fat join の図式を curry して展開すると元の図式に戻る。
方針：頂点の条件を忘れた curry の同定と既存の太い slice の往復則を使う。
規約：固定条件の証明の選択には依存しない。
使われ方：Kerodon §4.6.6（Tag 04HY） の固定頂点の模型の普遍性の一方の逆則。 -/
lemma fixedFatConeUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ≫ F = SSet.const x)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ F = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry (fixedFatConeCurry F hx hp) = F := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry, fixedFatConeCurry_toLaxSlice, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_curry]

/-- 概要：固定頂点の錐の族を展開して curry すると元の族に戻る。
方針：展開の単射性と図式側の往復則を使う。
規約：A・K・X の充填性や非空性は仮定しない。
使われ方：Kerodon §4.6.6（Tag 04HY） の固定頂点の模型の普遍性の他方の逆則。 -/
lemma fixedFatConeCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    fixedFatConeCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_inl f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_inr f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_injective p x
  rw [fixedFatConeUncurry_curry]

/-- 概要：固定頂点の錐の族と両端を固定した fat join の図式は全単射で対応する。
方針：両端固定の curry と uncurry および二つの往復則をまとめる。
規約：任意パラメータでの普遍性であり、零単体の対応だけに制限しない。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の固定条件を保つ模型の比較。 -/
noncomputable def fixedFatConeHomEquiv {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) ≃
      {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ≫ F = SSet.const x ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ F = p} where
  toFun f := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_inl f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_inr f⟩
  invFun F := fixedFatConeCurry F.val F.property.1 F.property.2
  left_inv f := fixedFatConeCurry_uncurry f
  right_inv F := Subtype.ext (fixedFatConeUncurry_curry F.val F.property.1 F.property.2)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

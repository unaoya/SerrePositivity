module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeSections
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：頂点を固定した coherent な錐の切断模型と、その具体的な点。
方針：coslice 射影上の相対関手空間を用い、零単体と実際の持ち上げを同定する。
規約：Kan 性には元の単体集合の quasicategory 性だけを要求する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の錐の切断データ。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：底の図式を保つ持ち上げは相対関手空間の零単体と全単射で対応する。
方針：標準零単体との直積の第一射影の同型を使い、相対 curry と uncurry を往復する。
規約：全ての単体集合の射を扱い、充填性を仮定しない。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS） の切断模型の具体的な点。 -/
noncomputable def relativeFunctorVertexEquiv {K E B : SSet.{u}} (p : E ⟶ B) (a : K ⟶ B) :
    {g : K ⟶ E // g ≫ p = a} ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) _⦋0⦌ where
  toFun g := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (fst K (Δ[0] : SSet.{u}) ≫ g.val) (by
    rw [Category.assoc, g.property]))
  invFun b := ⟨inv (fst K (Δ[0] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm b), by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, ← Category.assoc,
        IsIso.inv_hom_id, Category.id_comp]⟩
  left_inv g := by
    apply Subtype.ext
    change inv (fst K (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry _ _))) = g.val
    rw [Equiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  right_inv b := by
    apply SSet.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

variable {K X : SSet.{u}}

/-- 概要：図式 p と頂点 x に対する coherent な錐の切断模型。
方針：x の coslice 射影の上で p に重なる相対関手空間を取る。
規約：高次の模型は相対関手のパラメータ付き族で与える。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の錐から比較の標的の点を得る準備。 -/
def coherentConeSectionSpace (p : K ⟶ X) (x : X _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p

/-- 概要：quasicategory 内の図式と頂点に対する錐の切断模型は Kan 複体である。
方針：coslice 射影の left fibration 性と相対関手空間の Kan 性を使う。
規約：図式の始域 K に quasicategory 性を要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の coherent な錐の空間の充填性。 -/
instance coherentConeSectionSpace_kanComplex [Quasicategory X] (p : K ⟶ X)
    (x : X _⦋0⦌) : KanComplex (coherentConeSectionSpace p x) :=
  inferInstanceAs (KanComplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p))

/-- 概要：頂点を固定した coherent な錐と切断模型の零単体は全単射で対応する。
方針：coslice の切断との全単射と相対関手空間の零単体の全単射を合成する。
規約：左端の射を指定頂点に厳密に固定する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の実際の coherent な錐の点としての表示。 -/
noncomputable def fixedVertexConeSpaceEquiv (p : K ⟶ X) (x : X _⦋0⦌) :
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K ≫ c.val = SSet.yonedaEquiv.symm x} ≃
      (coherentConeSectionSpace p x) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSectionEquiv p x).trans
    (relativeFunctorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p)

/-- 概要：任意の coherent な錐はその頂点における切断模型の具体的な点を与える。
方針：錐を coslice の切断へ curry して、零単体の全単射を適用する。
規約：strict な錐への制限や追加の同値の選択は含まない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の比較ファイバーの底のデータ。 -/
noncomputable def coherentConeSectionPoint {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (coherentConeSectionSpace p c.vertex) _⦋0⦌ :=
  relativeFunctorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex)) p
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection_projection c⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

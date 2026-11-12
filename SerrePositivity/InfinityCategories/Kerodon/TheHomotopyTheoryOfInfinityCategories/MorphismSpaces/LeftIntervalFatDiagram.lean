module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatNaturality

/-!
概要：区間模型の族を、左に点を持つ fat join 図式へ展開する。
方針：左の点因子を補った円柱上で区間の族を評価し、固定端点を貼り合わせる。
規約：左の点は始点、右のパラメータ全体は終点に写す。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左 pinched 模型との比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：左の点因子を持つ円柱から区間とパラメータへ射影する。
方針：最初の直積の点成分を第二射影で忘れる。
規約：円柱は (Δ[0]×Δ[1])×A。
使われ方：Kerodon §4.6.6（Tag 04HY）、左 fat join 上での区間族の評価。 -/
def leftIntervalCylinderProjection (A : SSet.{u}) :
    ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ A ⟶ Δ[1] ⊗ A :=
  snd (Δ[0] : SSet.{u}) Δ[1] ▷ A

/-- 概要：区間とパラメータの直積に左の点成分を補う。
方針：区間に定値の点成分を添えてからパラメータと直積を取る。
規約：射影の厳密な逆として使う。
使われ方：Kerodon §4.6.6（Tag 04HY）、左 fat join 図式からの区間族の回収。 -/
def leftIntervalCylinderSection (A : SSet.{u}) :
    Δ[1] ⊗ A ⟶ ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ A :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 (Δ[1] : SSet.{u})) ▷ A

/-- 概要：左の点を補って忘れると元に戻る。
方針：各次数の成分を直接計算する。
規約：射の等式として成立する。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間族の回収の往復。 -/
lemma leftIntervalCylinderSection_projection (A : SSet.{u}) :
    leftIntervalCylinderSection A ≫ leftIntervalCylinderProjection A = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：左の点を忘れて補い直しても円柱は変わらない。
方針：標準零単体の各次数の単体の一意性を使う。
規約：点因子以外は恒等で保つ。
使われ方：Kerodon §4.6.6（Tag 04HY）、左 prism と円柱比較の同定。 -/
lemma leftIntervalCylinderProjection_section (A : SSet.{u}) :
    leftIntervalCylinderProjection A ≫ leftIntervalCylinderSection A = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨b, t⟩, a⟩
  apply Prod.ext
  · apply Prod.ext
    · apply stdSimplex.ext
      intro i
      apply Fin.ext
      change 0 = (b i).val
      have hb := (b i).isLt
      omega
    · rfl
  · rfl

/-- 概要：左の円柱の零端の射影は区間の零端への評価。
方針：各次数で区間成分を零に固定する。
規約：点因子は第二射影で忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY）、fat join の左端の貼り合わせ条件。 -/
lemma leftIntervalCylinderProjection_zero (A : SSet.{u}) :
    (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ A) ≫ leftIntervalCylinderProjection A =
      snd (Δ[0] : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：左の円柱の一端の射影は区間の一端への評価。
方針：各次数で区間成分を一に固定する。
規約：点因子は第二射影で忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY）、fat join の右端の貼り合わせ条件。 -/
lemma leftIntervalCylinderProjection_one (A : SSet.{u}) :
    (SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ A) ≫ leftIntervalCylinderProjection A =
      snd (Δ[0] : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：区間模型の族を左に点を持つ fat join 図式として展開する。
方針：円柱上の評価を固定端点の条件で左右の因子へ貼り合わせる。
規約：左の点は x、右因子は y に定値。
使われ方：Kerodon §4.6.6（Tag 04HY）、左写像空間の比較の逆の構成。 -/
noncomputable def leftIntervalFatDiagram {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc (SSet.yonedaEquiv.symm x) (SSet.const y)
    (leftIntervalCylinderProjection A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f) (by
      rw [← Category.assoc, leftIntervalCylinderProjection_zero, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero, SSet.comp_const]
      have he : fst (Δ[0] : SSet.{u}) A = SSet.const (stdSimplex.obj₀Equiv.symm 0) :=
        stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda]) (by
      rw [← Category.assoc, leftIntervalCylinderProjection_one, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, SSet.comp_const])

/-- 概要：左 fat join 展開は左の点上で x に一致する。
方針：fat join の左包含上の貼り合わせを計算する。
規約：族 f は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、左端の固定条件。 -/
lemma leftIntervalFatDiagram_inl {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] A ≫ leftIntervalFatDiagram f = SSet.yonedaEquiv.symm x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 概要：左 fat join 展開は右因子上で y に定値。
方針：fat join の右包含上の貼り合わせを計算する。
規約：族 f は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、右端の固定条件。 -/
lemma leftIntervalFatDiagram_inr {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] A ≫ leftIntervalFatDiagram f = SSet.const y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- 概要：左 fat join 展開を円柱に制限すると区間族の評価に一致する。
方針：円柱上の貼り合わせの計算則を使う。
規約：左の点因子は射影で忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY）、左展開の回収と自然性。 -/
lemma leftIntervalFatDiagram_cylinder {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] A ≫ leftIntervalFatDiagram f =
      leftIntervalCylinderProjection A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc _ _ _ _ _

/-- 概要：区間の族は左 fat join 展開の円柱から厳密に回収できる。
方針：円柱の式と切断・射影の往復を使う。
規約：元の族 f と射の等式で一致する。
使われ方：Kerodon §4.6.6（Tag 04HY）、左展開のホモトピーを区間模型へ戻す。 -/
lemma leftIntervalFatDiagram_recover {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    leftIntervalCylinderSection A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] A ≫ leftIntervalFatDiagram f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f := by
  rw [leftIntervalFatDiagram_cylinder, ← Category.assoc,
    leftIntervalCylinderSection_projection, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

module

public import SerrePositivity.InfinityCategories.F1B.PinchedIntervalComparison
public import SerrePositivity.InfinityCategories.F1.JoinEndpointComparison

/-!
概要：区間模型の族の右 fat join への展開。
方針：F1 の右模型の計算を狭い依存上で用い、相対 join 延長に接続する。
規約：左模型・straightening のモジュールを import しない。
使われ方：Kerodon §4.6.5–4.6.6、Prop 6.2.1.17 の pinched 模型への移行。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.PinchedInterval

/-- 概要：右の点を補った円柱を通常の区間とパラメータの直積へ戻す。
方針：標準零単体の成分を忘れ、残りの二因子を交換する。
規約：始域は (A×Δ[1])×Δ[0]。
使われ方：Kerodon §4.6.6、区間の族を fat join の円柱で評価する。 -/
def rightIntervalCylinderProjection (A : SSet.{u}) :
    (A ⊗ Δ[1]) ⊗ (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ A :=
  fst (A ⊗ Δ[1]) Δ[0] ≫ (β_ A Δ[1]).hom

/-- 概要：区間とパラメータの直積に右の点を補う。
方針：二因子を交換し、標準零単体の唯一の点を第三因子とする。
規約：この射の後に join の円柱比較を続けると右の prism 比較。
使われ方：Kerodon §4.6.6、fat join の図式から区間の族への回収。 -/
def rightIntervalCylinderSection (A : SSet.{u}) :
    Δ[1] ⊗ A ⟶ (A ⊗ Δ[1]) ⊗ (Δ[0] : SSet.{u}) :=
  (β_ Δ[1] A).hom ≫
    lift (𝟙 (A ⊗ Δ[1])) (SSet.const (stdSimplex.obj₀Equiv.symm 0))

/-- 概要：右の点を補ってから忘れると元の区間とパラメータに戻る。
方針：各次数の二つの成分を直接計算する。
規約：厳密な射の等式。
使われ方：Kerodon §4.6.6、区間の族の回収の往復。 -/
lemma rightIntervalCylinderSection_projection (A : SSet.{u}) :
    rightIntervalCylinderSection A ≫ rightIntervalCylinderProjection A = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：右の零単体の成分を忘れて補い直しても円柱は変わらない。
方針：標準零単体の任意の単体の全頂点の値が零であることを使う。
規約：二つの円柱の間の比較は厳密な同型。
使われ方：Kerodon §4.6.6、fat join の図式の回収の一意性。 -/
lemma rightIntervalCylinderProjection_section (A : SSet.{u}) :
    rightIntervalCylinderProjection A ≫ rightIntervalCylinderSection A = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, t⟩, b⟩
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro i
    apply Fin.ext
    change 0 = (b i).val
    have hb := (b i).isLt
    omega

/-- 概要：円柱の零端を区間へ戻すと零端点での評価になる。
方針：各次数で区間とパラメータの成分を計算する。
規約：右の零単体の成分は第一射影で忘れる。
使われ方：Kerodon §4.6.6、始点での貼り合わせ条件。 -/
lemma rightIntervalCylinderProjection_zero (A : SSet.{u}) :
    (SSet.ι₀ (X := A) ▷ (Δ[0] : SSet.{u})) ≫ rightIntervalCylinderProjection A =
      fst A Δ[0] ≫ prismEndpoint 0 A := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：円柱の一端を区間へ戻すと一端点での評価になる。
方針：各次数で区間の値を一に固定して計算する。
規約：右の零単体の成分は第一射影で忘れる。
使われ方：Kerodon §4.6.6、終点での貼り合わせ条件。 -/
lemma rightIntervalCylinderProjection_one (A : SSet.{u}) :
    (SSet.ι₁ (X := A) ▷ (Δ[0] : SSet.{u})) ≫ rightIntervalCylinderProjection A =
      fst A Δ[0] ≫ prismEndpoint 1 A := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：区間模型への族を両端固定の fat join の図式として展開する。
方針：円柱を区間へ戻して評価し、両端の定値条件により左右の因子を貼る。
規約：左因子 A は x に定値、右の点は y を表す。
使われ方：Kerodon §4.6.6、fat join 比較の同値を区間模型へ適用する。 -/
noncomputable def rightIntervalFatDiagram {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) : fatJoin A (Δ[0] : SSet.{u}) ⟶ X :=
  fatJoinDesc (SSet.const x) (SSet.yonedaEquiv.symm y)
    (rightIntervalCylinderProjection A ≫ intervalMappingUncurry f) (by
      rw [← Category.assoc, rightIntervalCylinderProjection_zero, Category.assoc,
        intervalFamily_zero, SSet.comp_const]) (by
      rw [← Category.assoc, rightIntervalCylinderProjection_one, Category.assoc,
        intervalFamily_one, SSet.comp_const]
      have he : snd A (Δ[0] : SSet.{u}) = SSet.const (stdSimplex.obj₀Equiv.symm 0) :=
        stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [he, const_point_comp_yoneda])

/-- 概要：展開した fat join 図式は左因子上で x に定値。
方針：fat join の貼り合わせの左包含を計算する。
規約：族 f は任意。
使われ方：Kerodon §4.6.6、左端の固定図式。 -/
lemma rightIntervalFatDiagram_inl {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinInl A Δ[0] ≫ rightIntervalFatDiagram f = SSet.const x :=
  fatJoinInl_desc _ _ _ _ _

/-- 概要：展開した fat join 図式は右の点上で y に一致。
方針：fat join の貼り合わせの右包含を計算する。
規約：右因子は標準零単体。
使われ方：Kerodon §4.6.6、右端の固定図式。 -/
lemma rightIntervalFatDiagram_inr {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinInr A Δ[0] ≫ rightIntervalFatDiagram f = SSet.yonedaEquiv.symm y :=
  fatJoinInr_desc _ _ _ _ _

/-- 概要：区間の族は展開した fat join 図式の円柱から回収できる。
方針：円柱上の貼り合わせ式と円柱の切断・射影の往復を使う。
規約：射の等式として回収する。
使われ方：Kerodon §4.6.6、fat join 上の比較を区間模型へ戻す式。 -/
lemma rightIntervalFatDiagram_recover {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    rightIntervalCylinderSection A ≫ fatJoinCylinder A Δ[0] ≫ rightIntervalFatDiagram f =
      intervalMappingUncurry f := by
  unfold rightIntervalFatDiagram
  rw [fatJoinCylinder_desc, ← Category.assoc, rightIntervalCylinderSection_projection,
    Category.id_comp]


end SerrePositivity.InfinityCategories.PinchedInterval

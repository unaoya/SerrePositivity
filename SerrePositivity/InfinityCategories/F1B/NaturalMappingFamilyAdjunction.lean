module

public import SerrePositivity.InfinityCategories.F1B.NaturalMappingFamilyComparison
public import SerrePositivity.InfinityCategories.F1B.MappingArrowNaturality

/-!
概要：族の前層の自然変換による随伴の写像空間判定。
方針：自然比較の表示定理で矢印空間の判定へ移し、各点の同値条件だけを使う。
規約：単位・余単位・全パラメータの全単射は入力しない。
使われ方：B1 の自然性を全パラメータの族の前層で表した存在判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
namespace NaturalMappingFamilyComparison
variable {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
variable (q : NaturalMappingFamilyComparison F G)

/-- 概要：表示された矢印比較の族への作用は元の自然変換の成分そのもの。
方針：任意の族の表示公式で raw なホモトピーの射を取り出す。
規約：非定値端点・任意のパラメータを許す。使われ方：入力した自然比較の回収。 -/
lemma transformation_h {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ F) b) :
    (q.transformation.app (Opposite.op A) ⟨a, b, H⟩).homotopy.h =
      (q.toMappingArrowComparison.mapHomotopy a b H).h :=
  congrArg (fun f : RightMappingFamily G A => f.homotopy.h) (q.transformation_app A ⟨a, b, H⟩)

/-- 概要：自然比較を各点の区間写像空間へ制限する。
方針：表示された矢印比較の普遍区間族で定める。
規約：作用は transformation_h で元の自然変換と厳密に一致。
使われ方：各点の同値性を述べる比較射。 -/
def intervalMap (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ⟶
      intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) :=
  q.toMappingArrowComparison.intervalMap x y

/-- 概要：各点の比較射は元の自然変換の任意の定値端点族への作用を表す。
方針：普遍区間族の公式と自然変換の raw な回収を使う。
規約：パラメータ A は任意、同値性は不要。
使われ方：各点の比較を自然変換から独立に選んでいないことの確認。 -/
lemma intervalMap_family_h {A : SSet.{u}} (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    (intervalFamilyHomotopy (f ≫ q.intervalMap x y)).h =
      (q.transformation.app (Opposite.op A)
        ⟨SSet.const x, SSet.const y, leftMappingIntervalHomotopy F x y f⟩).homotopy.h := by
  exact (q.toMappingArrowComparison.intervalMap_family_h x y f).trans
    (q.transformation_h (SSet.const x) (SSet.const y) (leftMappingIntervalHomotopy F x y f)).symm

/-- 概要：自然比較の各点の右 pinched 写像空間の射。
方針：区間模型との比較で移す。
規約：全パラメータの自然性は前層の自然変換が保持する。
使われ方：自然な pinched 写像空間の同値条件。 -/
def pinchedMap [Quasicategory X] [Quasicategory Y] (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    pinchedHom (F.app (Opposite.op ⦋0⦌) x) y ⟶ pinchedHom x (G.app (Opposite.op ⦋0⦌) y) :=
  q.toMappingArrowComparison.pinchedMap x y

/-- 概要：自然比較の各点がホモトピー同値である条件。
方針：自然変換から回収した各点の区間比較の同値性のみを要求する。
規約：全パラメータの同値性を仮定しない。使われ方：自然比較からの随伴構成。 -/
def IsPointwiseEquivalence : Prop := q.toMappingArrowComparison.IsPointwiseEquivalence

/-- 概要：各点で同値な自然な族の比較から随伴を構成する。
方針：自然比較の表示と指定単位版への接続を使う。
規約：入力には単位・余単位を含まない。使われ方：B1 の存在判定の逆方向。 -/
def adjunctionOfPointwiseEquivalence [Quasicategory X] [Quasicategory Y]
    (hq : q.IsPointwiseEquivalence) : QCatAdjunction F G :=
  q.toMappingArrowComparison.adjunctionOfPointwiseEquivalence hq

end NaturalMappingFamilyComparison

/-- 概要：随伴の存在は全端点の族に自然な各点の同値比較の存在と同値。
方針：自然比較と矢印比較の表示の両逆を使い、矢印比較の判定を移す。
規約：自然性は全パラメータに、同値条件は各点だけに要求する。
使われ方：B1 の族の前層を用いた自然な写像空間による判定。 -/
lemma qcat_nonempty_adjunction_iff_exists_naturalMappingFamilyComparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (G : Y ⟶ X) :
    Nonempty (QCatAdjunction F G) ↔
      ∃ q : NaturalMappingFamilyComparison F G, q.IsPointwiseEquivalence := by
  rw [qcat_nonempty_adjunction_iff_exists_mappingArrowComparison]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q.toNaturalMappingFamilyComparison, ?_⟩
    change q.toNaturalMappingFamilyComparison.toMappingArrowComparison.IsPointwiseEquivalence
    rwa [q.toNaturalMappingFamilyComparison_toMappingArrow]
  · rintro ⟨q, hq⟩
    exact ⟨q.toMappingArrowComparison, hq⟩

/-- 概要：自然な族の比較による随伴判定を右 pinched 模型で述べる。
方針：各点の模型比較で同値性を双方向に移す。
規約：自然性は前層の自然変換、各点の条件は実際のホモトピー逆の存在。
使われ方：B1 の pinchedHom による特徴づけの族の型。 -/
lemma qcat_nonempty_adjunction_iff_exists_naturalPinchedFamilyComparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (G : Y ⟶ X) :
    Nonempty (QCatAdjunction F G) ↔
      ∃ q : NaturalMappingFamilyComparison F G,
        ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), IsSimplicialHomotopyEquivalence (q.pinchedMap x y) := by
  rw [qcat_nonempty_adjunction_iff_exists_naturalMappingFamilyComparison]
  exact exists_congr (fun q => q.toMappingArrowComparison.isPointwiseEquivalence_iff_pinched)

end SerrePositivity.InfinityCategories

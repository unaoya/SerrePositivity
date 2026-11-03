module

public import SerrePositivity.InfinityCategories.F1B.Joins.JoinDiagonalSplit
public import SerrePositivity.InfinityCategories.Core.CoconeTransportPrism
public import SerrePositivity.InfinityCategories.Core.JoinTensorInterval
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorMiddle
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorRightPair

/-!
概要：join の左因子を第二の因子へ移す prism の構成と境界。
方針：左因子だけを区間付き対角で二重化し、join の結合を変える。
規約：時間は第一因子、右因子は全時刻で固定する。
使われ方：相対 join の局所余錐と指定変換の輸送を結ぶホモトピー。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：join の左因子をもう一つの左因子へ移す標準 prism。
方針：直積と join の比較、左因子の対角、結合同型を合成する。
規約：終点は join 全体の右包含。
使われ方：局所余錐を右端へ移す図式の準備。 -/
def joinShiftPrism (A B : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ join A B ⟶ join A (join A B) :=
  joinTensorLeft Δ[1] A B ≫ joinMap (joinDiagonal A) (𝟙 B) ≫
    (stableJoinAssociator A A B).hom

/-- 概要：prism の始点は最初の左因子と最後の右因子からなる包含。
方針：joinTensorLeft の端点と結合同型の中間因子の式を使う。
規約：右因子 B は内側の join の右因子へ入る。
使われ方：補正ホモトピーの元の局所余錐。 -/
lemma joinShiftPrism_zero (A B : SSet.{u}) :
    prismEndpoint 0 (join A B) ≫ joinShiftPrism A B =
      joinMap (𝟙 A) (joinInr A B) := by
  rw [joinShiftPrism, ← Category.assoc, stable_joinTensorLeft_prismEndpoint,
    ← Category.assoc, ← joinMap_comp, prismEndpoint_zero_joinDiagonal, Category.id_comp,
    stableJoinAssociator_middle]

/-- 概要：prism の終点は join 全体の右包含。
方針：左因子を対角の終点に写し、結合同型の後二因子の式を使う。
規約：元の join 全体を保持する。
使われ方：右端の図式への補正の終点。 -/
lemma joinShiftPrism_one (A B : SSet.{u}) :
    prismEndpoint 1 (join A B) ≫ joinShiftPrism A B = joinInr A (join A B) := by
  rw [joinShiftPrism, ← Category.assoc, stable_joinTensorLeft_prismEndpoint,
    ← Category.assoc, ← joinMap_comp, prismEndpoint_one_joinDiagonal, Category.id_comp,
    stableJoinAssociator_rightPair]

/-- 概要：prism の左境界は A の区間付き対角の後に内側の左包含を入れた射。
方針：左因子での直積比較の式と結合同型の先頭二因子の式を使う。
規約：この境界が指定変換を全パラメータで保持する。
使われ方：輸送の diagram フィールドの照合。 -/
lemma joinShiftPrism_left (A B : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ◁ joinInl A B) ≫ joinShiftPrism A B =
      joinDiagonal A ≫ joinMap (𝟙 A) (joinInl A B) := by
  rw [joinShiftPrism, ← Category.assoc, joinTensorLeft_inl,
    ← Category.assoc, joinInl_joinMap, Category.assoc, stableJoinAssociator_inl]

/-- 概要：prism の右境界は時間によらず B を同じ右端へ入れる射。
方針：右因子での直積比較と結合同型の右端の式を使う。
規約：固定条件は raw な単体集合の射の等式。
使われ方：輸送の fixedVertex フィールドの照合。 -/
lemma joinShiftPrism_right (A B : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ◁ joinInr A B) ≫ joinShiftPrism A B =
      snd (Δ[1] : SSet.{u}) B ≫ joinInr A B ≫ joinInr A (join A B) := by
  rw [joinShiftPrism, ← Category.assoc, joinTensorLeft_inr,
    Category.assoc, ← Category.assoc (joinInr _ _), joinInr_joinMap, Category.id_comp,
    stableJoinAssociator_inr]

/-- 概要：左直積比較は join の左右の係数の射と可換。
方針：補った直積の二成分に射を作用させる。
規約：時間を含む第一因子 P は任意。
使われ方：prism の係数に関する自然性。 -/
lemma joinTensorLeft_factors {A A' B B' : SSet.{u}} (P : SSet.{u})
    (f : A ⟶ A') (g : B ⟶ B') :
    (P ◁ joinMap f g) ≫ joinTensorLeft P A' B' =
      joinTensorLeft P A B ≫ joinMap (P ◁ f) g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨p, ⟨l, a, b⟩⟩
  change (⟨l, (Join.augTensorEquiv P A' l.val).symm
      (Join.augMap P (Join.prefixIncl (n + 1) l.val _) p, Join.augHom f l.val a),
      Join.augHom g (n + 1 - l.val) b⟩ : Join.Simplex (P ⊗ A') B' n) =
    ⟨l, Join.augHom (P ◁ f) l.val ((Join.augTensorEquiv P A l.val).symm
      (Join.augMap P (Join.prefixIncl (n + 1) l.val _) p, a)),
      Join.augHom g (n + 1 - l.val) b⟩
  apply Join.Simplex.ext _ _ (by apply Fin.ext; rfl)
  · exact (Join.augTensorEquiv_symm_augHomRight P f l.val _ a).symm
  · rfl

/-- 概要：左因子を移す prism は両係数の射に自然。
方針：直積比較・対角・結合同型の三つの自然性を合わせる。
規約：時間は恒等射で保つ。
使われ方：標準単体での prism の検査を一般の係数へ移す。 -/
lemma joinShiftPrism_naturality {A A' B B' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') :
    ((Δ[1] : SSet.{u}) ◁ joinMap f g) ≫ joinShiftPrism A' B' =
      joinShiftPrism A B ≫ joinMap f (joinMap f g) := by
  have h : joinMap (((Δ[1] : SSet.{u}) ◁ f) ≫ joinDiagonal A') g =
      joinMap (joinDiagonal A) (𝟙 B) ≫ joinMap (joinMap f f) g := by
    rw [joinDiagonal_naturality, ← joinMap_comp, Category.id_comp]
  simp only [joinShiftPrism]
  rw [← Category.assoc, joinTensorLeft_factors, Category.assoc,
    ← Category.assoc (joinMap _ _), ← joinMap_comp, Category.comp_id, h,
    Category.assoc, stableJoinAssociator_naturality]
  simp only [Category.assoc]

/-- 概要：左因子の移動を型付きの単体的ホモトピーとして束ねる。
方針：時間を第二因子へ直し、prism の両端の等式を使う。
規約：標的は join A (join A B)。相対 join への持ち上げは別に可換性を要する。
使われ方：境界を保持した図式のホモトピーへの後合成。 -/
def joinShiftHomotopy (A B : SSet.{u}) :
    SSet.Homotopy (joinMap (𝟙 A) (joinInr A B)) (joinInr A (join A B)) where
  h := (β_ (join A B) (Δ[1] : SSet.{u})).hom ≫ joinShiftPrism A B
  h₀ := by
    change prismEndpoint 0 (join A B) ≫ joinShiftPrism A B = _
    exact joinShiftPrism_zero A B
  h₁ := by
    change prismEndpoint 1 (join A B) ≫ joinShiftPrism A B = _
    exact joinShiftPrism_one A B
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories

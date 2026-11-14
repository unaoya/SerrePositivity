module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation
public import SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraDerivedInfinity

/-!
# 一対象の自由 dg 圏からの自由 dg 代数

概要：自由 dg 圏の一対象の自己準同型を自由モノイド対象に束ねる。
方針：有限 path の実直和と生成辺についての普遍性を再利用する。
規約：D の一対象 dg 圏の原本を直接 import し、複製しない。
使われ方：射影モデル構造を非可換 dg 代数へ転送する自由・忘却随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped MonObj
variable {R : Type u} [CommRing R]

/-- 概要：一対象 quiver の実 path 代数。
方針：自由 dg 圏の単位・合成とその既存の三律を束ねる。
規約：空 path を単位とする非可換代数。
使われ方：自由 dg 代数関手の対象作用。 -/
def freeObject (K : Complex R) : Mon (Complex R) where
  X := FreeDGCategory.homComplex R PUnit.{1} (fun _ _ => K) .unit .unit
  mon := {
    one := FreeDGCategory.unitInclusion R PUnit.{1} (fun _ _ => K) .unit
    mul := FreeDGCategory.composition R PUnit.{1} (fun _ _ => K) .unit .unit .unit
    one_mul := FreeDGCategory.composition_left_unit R PUnit.{1} (fun _ _ => K) .unit .unit
    mul_one := FreeDGCategory.composition_right_unit R PUnit.{1} (fun _ _ => K) .unit .unit
    mul_assoc := FreeDGCategory.composition_assoc R PUnit.{1} (fun _ _ => K)
      .unit .unit .unit .unit }

/-- 概要：元の複体を自由代数の長さ一の生成辺へ送る。
方針：自由 dg 圏の edgeInclusion を使う。
規約：底の chain map 自身を保持する。
使われ方：自由・忘却随伴の単位。 -/
def generator (K : Complex R) : K ⟶ (freeObject K).X :=
  FreeDGCategory.edgeInclusion R PUnit.{1} (fun _ _ => K) .unit .unit

/-- 概要：生成辺の chain map を代数射へ拡張する。
方針：D の原本の一対象 dg 圏へ自由 dg 関手を拡張する。
規約：元の標的モノイドの積を使う。
使われ方：自由代数の普遍性の逆写像。 -/
def lift (K : Complex R) (B : Mon (Complex R)) (f : K ⟶ B.X) : freeObject K ⟶ B :=
  let F := FreeDGCategory.lift R PUnit.{1} (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) (fun _ _ => K)
    (fun _ => .star) (fun _ _ => f)
  Mon.Hom.mk' (F.map .unit .unit) (F.map_id .unit) (F.map_comp .unit .unit .unit)

/-- 概要：自由拡張は元の生成辺射を回収する。
方針：自由 dg 圏の生成辺公式。
規約：底の同じ chain map の厳密等式。
使われ方：自由 Hom 同値の片側の逆則。 -/
@[reassoc (attr := simp)]
lemma generator_lift (K : Complex R) (B : Mon (Complex R)) (f : K ⟶ B.X) :
    generator K ≫ (lift K B f).hom = f :=
  FreeDGCategory.lift_edge R PUnit.{1} (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) (fun _ _ => K)
    (fun _ => .star) (fun _ _ => f) .unit .unit

/-- 概要：自由代数射は元の生成辺で決まる。
方針：有限 path に帰納し、単位と積の保存で全直和成分を比較する。
規約：対象の集合は一対象のまま固定する。
使われ方：自由拡張の一意性と関手法則。 -/
@[ext]
lemma free_hom_ext (K : Complex R) {B : Mon (Complex R)} {f g : freeObject K ⟶ B}
    (h : generator K ≫ f.hom = generator K ≫ g.hom) : f = g := by
  apply Mon.Hom.ext
  apply FreeDGCategory.homComplex_ext R PUnit.{1} (fun _ _ => K) .unit .unit
  intro p
  cases p with
  | inl e =>
    change η[(freeObject K).X] ≫ f.hom = η[(freeObject K).X] ≫ g.hom
    rw [IsMonHom.one_hom f.hom, IsMonHom.one_hom g.hom]
  | inr w =>
    induction w with
    | nil => exact h
    | cons b w ih =>
      cases b
      rw [← FreeDGCategory.composition_edge_path R PUnit.{1} (fun _ _ => K)
        .unit .unit .unit w, Category.assoc, Category.assoc]
      change (_ ⊗ₘ _) ≫ μ[(freeObject K).X] ≫ f.hom =
        (_ ⊗ₘ _) ≫ μ[(freeObject K).X] ≫ g.hom
      erw [IsMonHom.mul_hom f.hom, IsMonHom.mul_hom g.hom, ← Category.assoc,
        ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      change ((generator K ≫ f.hom) ⊗ₘ _) ≫ _ = ((generator K ≫ g.hom) ⊗ₘ _) ≫ _
      rw [h, ih]

/-- 概要：自由代数からの射と元の複体からの射の全 Hom 同値。
方針：生成辺への制限と自由拡張を厳密な両逆にする。
規約：標的は元の Mon (Complex R)。
使われ方：自由・忘却随伴を構成する。 -/
def freeHomEquiv (K : Complex R) (B : Mon (Complex R)) :
    (freeObject K ⟶ B) ≃ (K ⟶ B.X) where
  toFun f := generator K ≫ f.hom
  invFun := lift K B
  left_inv f := free_hom_ext K (by simp)
  right_inv f := generator_lift K B f

/-- 概要：生成辺による Hom 同値は標的で自然。
方針：元の chain map の合成の結合則。
規約：同じ代数射の後合成を使う。
使われ方：自由関手と随伴の構成。 -/
lemma freeHomEquiv_naturality (K : Complex R) (B C : Mon (Complex R))
    (g : B ⟶ C) (h : freeObject K ⟶ B) :
    freeHomEquiv K C (h ≫ g) = freeHomEquiv K B h ≫ g.hom :=
by
  change generator K ≫ (h.hom ≫ g.hom) = (generator K ≫ h.hom) ≫ g.hom
  exact (Category.assoc _ _ _).symm

/-- 概要：元の有限 path 自由 dg 代数関手。
方針：全 Hom 同値と標的自然性から関手法則を導く。
規約：対象作用は freeObject 自身。
使われ方：球面・円盤の自由像による生成射。 -/
def freeFunctor : Complex R ⥤ Mon (Complex R) :=
  Adjunction.leftAdjointOfEquiv (G := Mon.forget (Complex R))
    freeHomEquiv freeHomEquiv_naturality

/-- 概要：自由 dg 代数と底の複体の実随伴。
方針：生成辺による Hom 同値を随伴へ束ねる。
規約：標的は元の Mon (Complex R)。
使われ方：射影モデル構造の右転送。 -/
def freeForgetAdjunction : freeFunctor (R := R) ⊣ Mon.forget (Complex R) :=
  Adjunction.adjunctionOfEquivLeft (G := Mon.forget (Complex R))
    freeHomEquiv freeHomEquiv_naturality

/-- 概要：自由関手の対象は元の有限 path 代数。
方針：構成を展開する。
規約：底の複体も厳密に一致。
使われ方：テンソル冪表示との照合。 -/
lemma freeFunctor_obj (K : Complex R) : freeFunctor.obj K = freeObject K := rfl

/-- 概要：自由関手の射は生成辺の元の射の自由拡張。
方針：Hom 同値からの関手構成を展開する。
規約：始域・終域の元の複体を保持する。
使われ方：生成射の実自由像の照合。 -/
lemma freeFunctor_map {K L : Complex R} (f : K ⟶ L) :
    freeFunctor.map f = lift K (freeObject L) (f ≫ generator L) := by
  change lift K (freeObject L) (f ≫ generator L ≫ 𝟙 _) = _
  rw [Category.comp_id]

/-- 概要：随伴の単位は元の生成辺の包含。
方針：随伴を定めた Hom 同値を恒等射へ適用する。
規約：元の複体からの chain map 自身の等式。
使われ方：自由 cell の生成元の追跡。 -/
lemma freeForgetAdjunction_unit (K : Complex R) :
    freeForgetAdjunction.unit.app K = generator K := by
  change generator K ≫ 𝟙 _ = _
  exact Category.comp_id _

end SerrePositivity.EInfinity.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.3.15" (partial := component) "仮定：通常可換環 R の複体と厳密な結合的 dg 代数（Lean が強い：k=1 の通常圏の自由性の場合）。結論：tensor algebra による freeFunctor が忘却の左随伴となる（(1) の通常圏模型の自由性の部分に一致）。HA の局所化後の AlgEₖ との比較、全 k の自由性、(2) の反復 Bar と懸垂の同値は含まれない。"] _root_.SerrePositivity.EInfinity.DGAlgebra.freeForgetAdjunction

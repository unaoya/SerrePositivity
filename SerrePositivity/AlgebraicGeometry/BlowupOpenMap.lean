module

public import SerrePositivity.AlgebraicGeometry.BlowupOverSchemeExt
public import SerrePositivity.AlgebraicGeometry.BlowupAffineOpenMap
public import SerrePositivity.AlgebraicGeometry.AffineIdealPullback
public import SerrePositivity.AlgebraicGeometry.OpenComparisonBase

/-!
概要：KST §5、Stacks 080Y の任意の開埋め込みによる通常 blowup の比較射。
方針：始域の全アフィン開集合上の比較を一般基底上の一意性で自然化し、余極限へ貼り合わせる。
規約：開埋め込みの始域はアフィンと仮定しない。
使われ方：二段目の blowup のアフィン基底上への制限を大域の対象へ送る。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X Y : Scheme.{u}} (K : Y.IdealSheafData) (j : X ⟶ Y) [IsOpenImmersion j]

omit [IsOpenImmersion j] in
/--
概要：開埋め込みの始域のアフィン開集合上の逆像中心の環イデアル。
方針：イデアル層の逆像の合成則と標準アフィン Spec での切断公式を使う。
規約：KST §5、Stacks 080Y、始域の実際の切断イデアル。
使われ方：全アフィン局所モデルの中心比較射。
-/
theorem blowupOpenComponent_center (V : X.affineOpens) :
    specIdealEquiv Γ(X, V.1) (K.comap (V.2.fromSpec ≫ j)) = (K.comap j).ideal V := by
  rw [Scheme.IdealSheafData.comap_comp, specIdealEquiv_comap_fromSpec]

set_option backward.isDefEq.respectTransparency false in
/--
概要：開埋め込みの始域の一つのアフィン blowup モデルから標的の一般 blowup への比較。
方針：等しい中心の係数比較と合成アフィン開埋め込みの比較射を使う。
規約：KST §5、Stacks 080Y、始域は逆像イデアル層の局所モデル。
使われ方：一般の開埋め込みによる blowup 比較射の局所成分。
-/
def blowupOpenComponent (V : X.affineOpens) : affineBlowupModel (K.comap j) V ⟶ blowup K :=
  affineBlowupCenterMap (specIdealEquiv Γ(X, V.1) (K.comap (V.2.fromSpec ≫ j)))
    ((K.comap j).ideal V) (RingHom.id _)
    (by simpa only [Ideal.map_id] using blowupOpenComponent_center K j V) ≫
      blowupAffineOpenMap (V.2.fromSpec ≫ j) K

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の開埋め込みのアフィン局所比較射は基底上で可換。
方針：二つの中心比較射の構造射公式と恒等係数写像を使う。
規約：KST §5、Stacks 080Y、基底は Y。
使われ方：局所比較射の自然性と大域構造射の交換式。
-/
@[reassoc] theorem blowupOpenComponent_base (V : X.affineOpens) :
    blowupOpenComponent K j V ≫ blowupπ K = affineBlowupModelToBase (K.comap j) V ≫ j := by
  have h := centerComparison_id_openMap_base (V.2.fromSpec ≫ j) K ((K.comap j).ideal V)
    (blowupOpenComponent_center K j V)
  change blowupOpenComponent K j V ≫ blowupπ K =
    affineBlowupπ ((K.comap j).ideal V) ≫ (V.2.fromSpec ≫ j) at h
  simpa only [affineBlowupModelToBase, affineBlowupModelπ, IsAffineOpen.fromSpec,
    Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
/--
概要：開埋め込みによるアフィン局所比較射はアフィン開包含と両立する。
方針：一般基底上の blowup を標的とする射の一意性と構造射の交換式を使う。
規約：KST §5、Stacks 080Y、自然性は実際の射の等式。
使われ方：全アフィン局所図式の余極限への比較。
-/
theorem blowupOpenComponent_naturality {V W : X.affineOpens} (h : V ≤ W) :
    affineBlowupModelMap (K.comap j) h ≫ blowupOpenComponent K j W =
      blowupOpenComponent K j V := by
  apply affineBlowup_over_scheme_hom_ext K (V.2.fromSpec ≫ j) ((K.comap j).ideal V)
    (blowupOpenComponent_center K j V)
  · rw [Category.assoc, blowupOpenComponent_base, ← Category.assoc, affineBlowupModelMap_toBase]
    simp only [affineBlowupModelToBase, affineBlowupModelπ, IsAffineOpen.fromSpec, Category.assoc]
  · rw [blowupOpenComponent_base]
    simp only [affineBlowupModelToBase, affineBlowupModelπ, IsAffineOpen.fromSpec, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/--
概要：開埋め込みによる全アフィン blowup 局所モデルから標的 blowup への余錐。
方針：アフィン局所比較射と包含に関する自然性を束ねる。
規約：KST §5、Stacks 080Y、添字は全アフィン開集合。
使われ方：一般の開埋め込みによる比較射を余極限から構成する。
-/
def blowupOpenMapCocone : Cocone (affineBlowupDiagram (K.comap j)) where
  pt := blowup K
  ι := { app := blowupOpenComponent K j
         naturality := fun V W h => by
           change affineBlowupModelMap (K.comap j) (leOfHom h) ≫ blowupOpenComponent K j W =
             blowupOpenComponent K j V ≫ 𝟙 _
           rw [Category.comp_id]
           exact blowupOpenComponent_naturality K j (leOfHom h) }

/--
概要：任意の開埋め込みによる通常 blowup の実際の比較射。
方針：全アフィン局所比較の余錐から、スキームの余極限の射を取る。
規約：KST §5、Stacks 080Y、始域のアフィン性・Noether 性を要求しない。
使われ方：局所的に構成した二段 blowup の支配射を大域の二段目へ送る。
-/
def blowupOpenMap : blowup (K.comap j) ⟶ blowup K :=
  colimit.desc _ (blowupOpenMapCocone K j)

/--
概要：開埋め込みによる大域比較射は各アフィン局所比較に制限される。
方針：余極限の標準射と余錐の構成射の公式を使う。
規約：KST §5、Stacks 080Y、元のアフィン局所モデルを保持する。
使われ方：大域構造射の交換式の確認。
-/
@[reassoc] theorem blowupAffineι_blowupOpenMap (V : X.affineOpens) :
    blowupAffineι (K.comap j) V ≫ blowupOpenMap K j = blowupOpenComponent K j V :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の開埋め込みによる blowup 比較射は基底の開埋め込みと可換。
方針：始域の全アフィン局所モデルで構造射公式を比較する。
規約：KST §5、Stacks 080Y、Y への実際の射の等式。
使われ方：Noether 基底上の二段 blowup の支配の大域化。
-/
@[reassoc] theorem blowupOpenMap_base :
    blowupOpenMap K j ≫ blowupπ K = blowupπ (K.comap j) ≫ j := by
  apply colimit.hom_ext
  intro V
  change blowupAffineι (K.comap j) V ≫ blowupOpenMap K j ≫ blowupπ K =
    blowupAffineι (K.comap j) V ≫ blowupπ (K.comap j) ≫ j
  rw [blowupAffineι_blowupOpenMap_assoc, blowupOpenComponent_base, blowupAffineι_π_assoc]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

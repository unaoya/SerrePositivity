module

public import SerrePositivity.DifferentialGraded.Algebras.ColimitInput
public import SerrePositivity.DifferentialGraded.Algebras.ColimitLaws
public import Mathlib.CategoryTheory.Limits.Creates

/-!
# 底の余極限への dg モノイド構造の降下

概要：単位・二重・三重入力が保存する底の余極限を dg 代数へ持ち上げる。
方針：単位と積を普遍射で降ろし、共同全射な入力で三律を検査する。
規約：一般の余極限の忘却保存を仮定しない。
使われ方：filtered 余極限と分裂 coequalizer、転送の小対象性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.CategoryTheory.MonObj
variable {R : Type u} [CommRing R] {J : Type w} [Category.{v} J]
  (F : J ⥤ Mon (Complex R)) (c : Cocone (F ⋙ Mon.forget (Complex R))) (hc : IsColimit c)
  [PreservesColimit (F ⋙ Mon.forget (Complex R)) _root_.SerrePositivity.DGAlgebra.unitInput]
  [PreservesColimit (F ⋙ Mon.forget (Complex R)) _root_.SerrePositivity.DGAlgebra.binaryInput]
  [PreservesColimit (F ⋙ Mon.forget (Complex R)) _root_.SerrePositivity.DGAlgebra.ternaryInput]

/-- 概要：単位を元の底の余錐へ送る余錐。
方針：各代数の単位を構造射へ合成する。
規約：元の頂点を保持する。
使われ方：降りる単位の普遍射。 -/
def unitCocone : Cocone ((F ⋙ Mon.forget (Complex R)) ⋙ _root_.SerrePositivity.DGAlgebra.unitInput) where
  pt := c.pt
  ι.app j := η[(F.obj j).X] ≫ c.ι.app j
  ι.naturality i j f := by
    have h := c.w f
    change (F.map f).hom ≫ c.ι.app j = c.ι.app i at h
    change 𝟙 _ ≫ (η[(F.obj j).X] ≫ c.ι.app j) =
      (η[(F.obj i).X] ≫ c.ι.app i) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, ← h, ← Category.assoc,
      IsMonHom.one_hom (F.map f).hom]


/-- 概要：積を元の底の余錐へ送る余錐。
方針：各代数の積を構造射へ合成する。
規約：二重入力の順序を保つ。
使われ方：降りる積の普遍射。 -/
def multiplicationCocone : Cocone ((F ⋙ Mon.forget (Complex R)) ⋙ _root_.SerrePositivity.DGAlgebra.binaryInput) where
  pt := c.pt
  ι.app j := μ[(F.obj j).X] ≫ c.ι.app j
  ι.naturality i j f := by
    change ((F.map f).hom ⊗ₘ (F.map f).hom) ≫ (μ[(F.obj j).X] ≫ c.ι.app j) =
      (μ[(F.obj i).X] ≫ c.ι.app i) ≫ 𝟙 _
    have h := c.w f
    change (F.map f).hom ≫ c.ι.app j = c.ι.app i at h
    rw [Category.comp_id, ← IsMonHom.mul_hom_assoc (F.map f).hom, h]

/-- 概要：底の余極限へ降りる単位。
方針：定数単位入力の余極限の普遍射。
規約：元の複体の射。
使われ方：余極限 dg 代数の単位。 -/
def colimitOne : 𝟙_ (Complex R) ⟶ c.pt :=
  (isColimitOfPreserves _root_.SerrePositivity.DGAlgebra.unitInput hc).desc (_root_.SerrePositivity.DGAlgebra.unitCocone F c)

/-- 概要：底の余極限へ降りる積。
方針：二重入力の余極限の普遍射。
規約：元の複体の射。
使われ方：余極限 dg 代数の積。 -/
def colimitMul : c.pt ⊗ c.pt ⟶ c.pt :=
  (isColimitOfPreserves _root_.SerrePositivity.DGAlgebra.binaryInput hc).desc (_root_.SerrePositivity.DGAlgebra.multiplicationCocone F c)

omit [PreservesColimit (F ⋙ Mon.forget (Complex R)) _root_.SerrePositivity.DGAlgebra.binaryInput]
  [PreservesColimit (F ⋙ Mon.forget (Complex R)) _root_.SerrePositivity.DGAlgebra.ternaryInput] in
/-- 概要：構造射は降りた単位を保つ。
方針：普遍射の構造射公式。
規約：元の単位の厳密等式。
使われ方：モノイド三律の検査と構造射の束ね。 -/
@[reassoc]
lemma colimitOne_fac (j : J) : η[(F.obj j).X] ≫ c.ι.app j = _root_.SerrePositivity.DGAlgebra.colimitOne F c hc := by
  have h := (isColimitOfPreserves _root_.SerrePositivity.DGAlgebra.unitInput hc).fac (_root_.SerrePositivity.DGAlgebra.unitCocone F c) j
  change 𝟙 _ ≫ _root_.SerrePositivity.DGAlgebra.colimitOne F c hc = η[(F.obj j).X] ≫ c.ι.app j at h
  simpa only [Category.id_comp] using h.symm

omit [PreservesColimit (F ⋙ Mon.forget (Complex R)) _root_.SerrePositivity.DGAlgebra.unitInput]
  [PreservesColimit (F ⋙ Mon.forget (Complex R)) _root_.SerrePositivity.DGAlgebra.ternaryInput] in
/-- 概要：構造射は降りた積を保つ。
方針：普遍射の構造射公式。
規約：元の積の厳密等式。
使われ方：モノイド三律の検査と構造射の束ね。 -/
@[reassoc]
lemma colimitMul_fac (j : J) : μ[(F.obj j).X] ≫ c.ι.app j =
    (c.ι.app j ⊗ₘ c.ι.app j) ≫ _root_.SerrePositivity.DGAlgebra.colimitMul F c hc :=
  ((isColimitOfPreserves _root_.SerrePositivity.DGAlgebra.binaryInput hc).fac (_root_.SerrePositivity.DGAlgebra.multiplicationCocone F c) j).symm

/-- 概要：底の余極限の頂点の dg モノイド。
方針：三つの共同全射な入力で公理を検査する。
規約：底の頂点・単位・積は元の普遍射。
使われ方：忘却による余極限の創出。 -/
def colimitObject : Mon (Complex R) where
  X := c.pt
  mon := _root_.SerrePositivity.DGAlgebra.monoidOfJointlyEpic c.pt (fun j => F.obj j) (fun j => c.ι.app j)
    (_root_.SerrePositivity.DGAlgebra.colimitOne F c hc) (_root_.SerrePositivity.DGAlgebra.colimitMul F c hc) (_root_.SerrePositivity.DGAlgebra.colimitOne_fac F c hc) (_root_.SerrePositivity.DGAlgebra.colimitMul_fac F c hc)
    (fun _ _ h => (isColimitOfPreserves (tensorLeft (𝟙_ (Complex R))) hc).hom_ext h)
    (fun _ _ h => (isColimitOfPreserves (tensorRight (𝟙_ (Complex R))) hc).hom_ext h)
    (fun _ _ h => (isColimitOfPreserves _root_.SerrePositivity.DGAlgebra.ternaryInput hc).hom_ext h)

/-- 概要：元の底の余錐を代数の余錐へ持ち上げる。
方針：単位と積を保つ構造射を束ねる。
規約：忘却後の余錐は元のものと厳密に一致。
使われ方：創出する余極限の候補。 -/
def colimitCocone : Cocone F where
  pt := _root_.SerrePositivity.DGAlgebra.colimitObject F c hc
  ι.app j := Mon.Hom.mk' (c.ι.app j) (_root_.SerrePositivity.DGAlgebra.colimitOne_fac F c hc j) (_root_.SerrePositivity.DGAlgebra.colimitMul_fac F c hc j)
  ι.naturality _ _ f := Mon.Hom.ext (c.ι.naturality f)

/-- 概要：底の普遍射を代数射へ上げる。
方針：単位・積の保存を保存された入力余極限で検査する。
規約：同じ底の普遍射を使う。
使われ方：持ち上げた余錐の普遍性。 -/
def colimitDesc (s : Cocone F) : (_root_.SerrePositivity.DGAlgebra.colimitCocone F c hc).pt ⟶ s.pt :=
  Mon.Hom.mk' (hc.desc ((Mon.forget (Complex R)).mapCocone s)) (by
    change _root_.SerrePositivity.DGAlgebra.colimitOne F c hc ≫ _ = _
    apply (isColimitOfPreserves _root_.SerrePositivity.DGAlgebra.unitInput hc).hom_ext
    intro j
    change 𝟙 _ ≫ (_root_.SerrePositivity.DGAlgebra.colimitOne F c hc ≫ _) = 𝟙 _ ≫ _
    rw [Category.id_comp, Category.id_comp, ← _root_.SerrePositivity.DGAlgebra.colimitOne_fac F c hc j, Category.assoc, hc.fac]
    exact IsMonHom.one_hom (s.ι.app j).hom) (by
    change _root_.SerrePositivity.DGAlgebra.colimitMul F c hc ≫ _ = (_ ⊗ₘ _) ≫ _
    apply (isColimitOfPreserves _root_.SerrePositivity.DGAlgebra.binaryInput hc).hom_ext
    intro j
    change (c.ι.app j ⊗ₘ c.ι.app j) ≫ _ = (c.ι.app j ⊗ₘ c.ι.app j) ≫ _
    rw [← _root_.SerrePositivity.DGAlgebra.colimitMul_fac_assoc, hc.fac, ← Category.assoc, tensorHom_comp_tensorHom, hc.fac]
    exact IsMonHom.mul_hom (s.ι.app j).hom)

/-- 概要：持ち上げた代数の余錐は余極限。
方針：底の普遍性と忘却の忠実性を使う。
規約：余極限の構造射自身を保つ。
使われ方：代数忘却の創出判定。 -/
def colimitIsColimit : IsColimit (_root_.SerrePositivity.DGAlgebra.colimitCocone F c hc) where
  desc := _root_.SerrePositivity.DGAlgebra.colimitDesc F c hc
  fac s j := Mon.Hom.ext (hc.fac ((Mon.forget (Complex R)).mapCocone s) j)
  uniq s m h := by
    apply Mon.Hom.ext
    apply hc.uniq ((Mon.forget (Complex R)).mapCocone s)
    intro j
    exact congrArg Mon.Hom.hom (h j)

/-- 概要：三入力が保存する底の余極限を忘却関手が作る。
方針：任意の底の余錐の持ち上げを同型反映で束ねる。
規約：図式ごとの保存だけを要求する。
使われ方：sifted 余極限と分裂 coequalizer。 -/
@[instance_reducible]
def forgetCreatesColimit : CreatesColimit F (Mon.forget (Complex R)) :=
  createsColimitOfReflectsIso (fun c hc => {
    liftedCocone := _root_.SerrePositivity.DGAlgebra.colimitCocone F c hc
    validLift := Iso.refl _
    makesColimit := _root_.SerrePositivity.DGAlgebra.colimitIsColimit F c hc })

end SerrePositivity.DGAlgebra

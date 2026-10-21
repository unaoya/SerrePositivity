module
public import SerrePositivity.KST.SConstruction.NecklaceInStructuralIso
public import SerrePositivity.KST.SConstruction.NecklaceWedgeCoherence

/-! # K 内の元の構造同型の自然性と coherent 法則
概要：元の固定端点の結合・左右単位が全可換三角形で自然となり、五角と三角を満たす。
方針：元の necklace 射への忠実な射影で、証明済みの native な法則を反映する。
規約：全高次単体と augmentation を保持。使われ方：cubical 余極限の合成の coherence。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- K 内の元の三重連結の結合同型は、全ての元の可換三角形について自然。 -/
lemma necklaceInAssociator_naturality {K : SSet.{u}} {w x y z : K _⦋0⦌}
    {T T' : NecklaceIn K w x} {U U' : NecklaceIn K x y} {V V' : NecklaceIn K y z}
    (f : T ⟶ T') (g : U ⟶ U') (h : V ⟶ V') :
    necklaceInWedgeMap (necklaceInWedgeMap f g) h ≫ (necklaceInAssociator T' U' V').hom =
      (necklaceInAssociator T U V).hom ≫ necklaceInWedgeMap f (necklaceInWedgeMap g h) :=
  NecklaceInHom.ext (necklaceAssociator_naturality f.necklaceHom g.necklaceHom h.necklaceHom)

/-- K 内の元の左単位は、全ての元の可換三角形について自然。 -/
lemma necklaceInLeftUnitor_naturality {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : NecklaceIn K x y} (f : T ⟶ U) :
    necklaceInWedgeMap (𝟙 (necklaceInPoint K x)) f ≫ (necklaceInLeftUnitor U).hom =
      (necklaceInLeftUnitor T).hom ≫ f :=
  NecklaceInHom.ext (necklaceLeftUnitor_naturality f.necklaceHom)

/-- K 内の元の右単位は、全ての元の可換三角形について自然。 -/
lemma necklaceInRightUnitor_naturality {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : NecklaceIn K x y} (f : T ⟶ U) :
    necklaceInWedgeMap f (𝟙 (necklaceInPoint K y)) ≫ (necklaceInRightUnitor U).hom =
      (necklaceInRightUnitor T).hom ≫ f :=
  NecklaceInHom.ext (necklaceRightUnitor_naturality f.necklaceHom)

/-- K 内の元の全四重連結で、元の結合同型は五角を満たす。 -/
lemma necklaceInAssociator_pentagon {K : SSet.{u}} {v w x y z : K _⦋0⦌}
    (T : NecklaceIn K v w) (U : NecklaceIn K w x) (V : NecklaceIn K x y)
    (W : NecklaceIn K y z) :
    necklaceInWedgeMap (necklaceInAssociator T U V).hom (𝟙 W) ≫
        (necklaceInAssociator T (necklaceInWedge U V) W).hom ≫
          necklaceInWedgeMap (𝟙 T) (necklaceInAssociator U V W).hom =
      (necklaceInAssociator (necklaceInWedge T U) V W).hom ≫
        (necklaceInAssociator T U (necklaceInWedge V W)).hom :=
  NecklaceInHom.ext (necklaceAssociator_pentagon T.necklace U.necklace V.necklace W.necklace)

/-- K 内の元の結合と一点の左右単位は三角を満たす。 -/
lemma necklaceInAssociator_triangle {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : NecklaceIn K x y) (U : NecklaceIn K y z) :
    (necklaceInAssociator T (necklaceInPoint K y) U).hom ≫
        necklaceInWedgeMap (𝟙 T) (necklaceInLeftUnitor U).hom =
      necklaceInWedgeMap (necklaceInRightUnitor T).hom (𝟙 U) :=
  NecklaceInHom.ext (necklaceAssociator_triangle T.necklace U.necklace)

end SerrePositivity.KST.SConstruction

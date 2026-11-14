module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceInStructuralIso
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeCoherence

/-! # K 内の元の構造同型の自然性と coherent 法則
概要：元の固定端点の結合・左右単位が全可換三角形で自然となり、五角と三角を満たす。
方針：元の necklace 射への忠実な射影で、証明済みの native な法則を反映する。
規約：全高次単体と augmentation を保持。使われ方：cubical 余極限の合成の coherence。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- K 内の元の三重連結の結合同型は、全ての元の可換三角形について自然。 -/
lemma necklaceInAssociator_naturality {K : SSet.{u}} {w x y z : K _⦋0⦌}
    {T T' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K w x} {U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} {V V' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z}
    (f : T ⟶ T') (g : U ⟶ U') (h : V ⟶ V') :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap f g) h ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator T' U' V').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator T U V).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap g h) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_naturality f.necklaceHom g.necklaceHom h.necklaceHom)

/-- K 内の元の左単位は、全ての元の可換三角形について自然。 -/
lemma necklaceInLeftUnitor_naturality {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x)) f ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInLeftUnitor U).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInLeftUnitor T).hom ≫ f :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_naturality f.necklaceHom)

/-- K 内の元の右単位は、全ての元の可換三角形について自然。 -/
lemma necklaceInRightUnitor_naturality {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K y)) ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInRightUnitor U).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInRightUnitor T).hom ≫ f :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_naturality f.necklaceHom)

/-- K 内の元の全四重連結で、元の結合同型は五角を満たす。 -/
lemma necklaceInAssociator_pentagon {K : SSet.{u}} {v w x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K v w) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K w x) (V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y)
    (W : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator T U V).hom (𝟙 W) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge U V) W).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap (𝟙 T) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator U V W).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) V W).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator T U (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge V W)).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_pentagon T.necklace U.necklace V.necklace W.necklace)

/-- K 内の元の結合と一点の左右単位は三角を満たす。 -/
lemma necklaceInAssociator_triangle {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K y) U).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap (𝟙 T) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInLeftUnitor U).hom =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInRightUnitor T).hom (𝟙 U) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_triangle T.necklace U.necklace)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInAssociator_naturality := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator_naturality

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInAssociator_pentagon := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator_pentagon

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInAssociator_triangle := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator_triangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInLeftUnitor_naturality := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInLeftUnitor_naturality

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInRightUnitor_naturality := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInRightUnitor_naturality

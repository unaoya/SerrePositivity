module

public import SerrePositivity.KST.Spectra.PointedBasedPathCalculus
public import SerrePositivity.KST.Spectra.PointedCurryingParameterComponents
public import SerrePositivity.KST.Spectra.PointedHomTransposeComponents

/-!
概要：元の基点固定区間族を curry・転置・内部 Hom の後合成へ移す。
方針：元の内部 Hom 同型の頂点公式を使い、同じ区間族へ同型の射を後合成する。
規約：区間の選択をやり直さない。使われ方：元の随伴構造比較の全 Hom への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 一点を標的とする内部 Hom は、元の点つき射の随伴で終対象になる。 -/
lemma hom_toPoint_unique (T : PointedSimplicialSet.{u}) {A : PointedSimplicialSet.{u}}
    (f g : A ⟶ PointedObject.basedHom T PointedObject.point) : f = g := by
  apply uncurry_injective
  exact PointedObject.point_isZero.eq_of_tgt _ _

/-- 一点を標的とする内部 Hom の全ての頂点は一致する。 -/
lemma hom_toPoint_vertex_unique (T : PointedSimplicialSet.{u})
    (v w : (PointedObject.basedHom T PointedObject.point).right _⦋0⦌) : v = w := by
  rw [← familyVertex_familyMap T PointedObject.point v,
    ← familyVertex_familyMap T PointedObject.point w]
  exact congrArg familyVertex (PointedObject.point_isZero.eq_of_tgt _ _)

namespace VerticalPath

/-- 頂点を指定の射へ移す元の内部 Hom の射で、基点固定区間そのものを移す。 -/
def basedMap {A E A' E' : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (H : VerticalPath (PointedObject.toPoint E) f g)
    (e : PointedObject.basedHom A E ⟶ PointedObject.basedHom A' E') (f' g' : A' ⟶ E')
    (hf : e.right.app (Opposite.op ⦋0⦌) (familyVertex f) = familyVertex f')
    (hg : e.right.app (Opposite.op ⦋0⦌) (familyVertex g) = familyVertex g') :
    VerticalPath (PointedObject.toPoint E') f' g' :=
  H.map (PointedObject.toPoint E') e 0 f' g' hf hg (hom_toPoint_unique A' _ _)
    (hom_toPoint_vertex_unique A' _ _)

/-- curry は元の基点固定区間族を、反復内部 Hom の同じ射による像へ移す。 -/
def basedCurry {K A V : PointedSimplicialSet.{u}} {f g : K ⊗ A ⟶ V}
    (H : VerticalPath (PointedObject.toPoint V) f g) :
    VerticalPath (PointedObject.toPoint ((ihom K).obj V)) (curry f) (curry g) :=
  H.basedMap (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K A V).hom (curry f) (curry g)
    (familyVertex_curry f).symm (familyVertex_curry g).symm

/-- 転置は元の基点固定区間族を、内部 Hom の同じ交換射による像へ移す。 -/
def basedTranspose {A U V : PointedSimplicialSet.{u}} {f g : A ⟶ (ihom U).obj V}
    (H : VerticalPath (PointedObject.toPoint ((ihom U).obj V)) f g) :
    VerticalPath (PointedObject.toPoint ((ihom A).obj V)) (transpose f) (transpose g) :=
  H.basedMap (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom (transpose f) (transpose g)
    (familyVertex_transpose f).symm (familyVertex_transpose g).symm

/-- 内部 Hom の標的への作用を、元の同じ区間の前合成と curry で構成する。 -/
def basedIhomMap (A : PointedSimplicialSet.{u}) {E V : PointedSimplicialSet.{u}}
    {f g : E ⟶ V} (H : VerticalPath (PointedObject.toPoint V) f g) :
    VerticalPath (PointedObject.toPoint ((ihom A).obj V)) ((ihom A).map f) ((ihom A).map g) := by
  have he (p : E ⟶ V) : curry ((ihom.ev A).app E ≫ p) = (ihom A).map p := by
    rw [curry_natural_right, ← uncurry_id_eq_ev, curry_uncurry, Category.id_comp]
  exact ((H.pre ((ihom.ev A).app E)).basedCurry).changeEndpoints (he f).symm (he g).symm

end VerticalPath

namespace VerticalChain

/-- 元の基点固定区間の有限鎖を curry で移す。 -/
lemma basedCurry {K A V : PointedSimplicialSet.{u}} {f g : K ⊗ A ⟶ V}
    (H : VerticalChain (PointedObject.toPoint V) f g) :
    VerticalChain (PointedObject.toPoint ((ihom K).obj V)) (curry f) (curry g) :=
  Relation.ReflTransGen.lift curry (fun _ _ ⟨H⟩ ↦ ⟨H.basedCurry⟩) f g H

/-- 元の基点固定区間の有限鎖を転置で移す。 -/
lemma basedTranspose {A U V : PointedSimplicialSet.{u}} {f g : A ⟶ (ihom U).obj V}
    (H : VerticalChain (PointedObject.toPoint ((ihom U).obj V)) f g) :
    VerticalChain (PointedObject.toPoint ((ihom A).obj V)) (transpose f) (transpose g) :=
  Relation.ReflTransGen.lift transpose (fun _ _ ⟨H⟩ ↦ ⟨H.basedTranspose⟩) f g H

/-- 内部 Hom の標的への作用は、元の基点固定区間の有限鎖を保持する。 -/
lemma basedIhomMap (A : PointedSimplicialSet.{u}) {E V : PointedSimplicialSet.{u}}
    {f g : E ⟶ V} (H : VerticalChain (PointedObject.toPoint V) f g) :
    VerticalChain (PointedObject.toPoint ((ihom A).obj V)) ((ihom A).map f) ((ihom A).map g) :=
  Relation.ReflTransGen.lift ((ihom A).map) (fun _ _ ⟨H⟩ ↦ ⟨H.basedIhomMap A⟩) f g H

end VerticalChain
end SerrePositivity.KST.Spectra.PointedMapping

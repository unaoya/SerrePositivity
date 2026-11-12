module

public import SerrePositivity.KST.Spectra.PointedVerticalPaths
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterStructure
public import SerrePositivity.KST.Spectra.SpectrumMorphisms

/-!
概要：元の点つき射の垂直区間を、前合成・後合成・懸垂に沿って移す。
方針：内部 Hom 上の厳密な可換正方形と元の頂点の自然性を使う。
規約：Kan 性不要。使われ方：相対厳密化の前段の修正を次段の境界へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
variable {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}

/-- 内部 Hom の射影の厳密な正方形は、元の垂直区間族を同じ射影の垂直区間へ送る。 -/
def map (H : VerticalPath p f g) {T' E' B' : PointedSimplicialSet.{u}} (q : E' ⟶ B')
    (e : PointedObject.basedHom T E ⟶ PointedObject.basedHom T' E')
    (b : PointedObject.basedHom T B ⟶ PointedObject.basedHom T' B') (f' g' : T' ⟶ E')
    (hf : e.right.app (Opposite.op ⦋0⦌) (familyVertex f) = familyVertex f')
    (hg : e.right.app (Opposite.op ⦋0⦌) (familyVertex g) = familyVertex g')
    (hsq : e ≫ PointedObject.basedHomMap T' q = PointedObject.basedHomMap T p ≫ b)
    (hb : b.right.app (Opposite.op ⦋0⦌) (familyVertex (f ≫ p)) =
      familyVertex (f' ≫ q)) : VerticalPath q f' g' where
  path := H.path ≫ e.right
  zero := by
    rw [← Category.assoc, H.zero]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    exact hf
  one := by
    rw [← Category.assoc, H.one]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    exact hg
  «over» := by
    have hs := congrArg Under.Hom.right hsq
    change e.right ≫ _ = _ ≫ b.right at hs
    rw [Category.assoc, hs, ← Category.assoc, H.over, SSet.const_comp, hb]

/-- 後合成の厳密な正方形に沿って、射影を固定する区間を移す。 -/
def post (H : VerticalPath p f g) {E' B' : PointedSimplicialSet.{u}}
    (q : E' ⟶ B') (v : E ⟶ E') (w : B ⟶ B') (h : v ≫ q = p ≫ w) :
    VerticalPath q (f ≫ v) (g ≫ v) := by
  have hs : PointedObject.basedHomMap T v ≫ PointedObject.basedHomMap T q =
      PointedObject.basedHomMap T p ≫ PointedObject.basedHomMap T w := by
    change (ihom T).map v ≫ (ihom T).map q = (ihom T).map p ≫ (ihom T).map w
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  have hc : (f ≫ p) ≫ w = (f ≫ v) ≫ q := by
    simp only [Category.assoc]
    rw [h]
  exact H.map q (PointedObject.basedHomMap T v) (PointedObject.basedHomMap T w)
    (f ≫ v) (g ≫ v) (familyVertex_post f v) (familyVertex_post g v) hs
    ((familyVertex_post (f ≫ p) w).trans (congrArg familyVertex hc))

/-- 源の前合成は、元の射影を固定する区間を保つ。 -/
def pre (H : VerticalPath p f g) {U : PointedSimplicialSet.{u}} (i : U ⟶ T) :
    VerticalPath p (i ≫ f) (i ≫ g) := by
  have hs : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E ≫ PointedObject.basedHomMap U p =
      PointedObject.basedHomMap T p ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i B := by
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact ((MonoidalClosed.pre i).naturality p).symm
  exact H.map p (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i B) (i ≫ f) (i ≫ g)
    (familyVertex_pre i f) (familyVertex_pre i g) hs
    ((familyVertex_pre i (f ≫ p)).trans (congrArg familyVertex (Category.assoc i f p).symm))

/-- 元の懸垂 Hom による頂点の像は、元の点つき射の懸垂。 -/
lemma familyVertex_suspension (f : T ⟶ E) :
    (suspensionHom T E).right.app (Opposite.op ⦋0⦌) (familyVertex f) =
      familyVertex (PointedSimplicialSet.circle.{u} ◁ f) := by
  simpa only [familyVertex_eq_pointedHomVertex] using pointedHomVertexEquiv_suspension f

/-- 垂直な点つき区間は、懸垂後も同じ懸垂した射影を全区間で固定する。 -/
def suspension (H : VerticalPath p f g) :
    VerticalPath (PointedSimplicialSet.circle.{u} ◁ p)
      (PointedSimplicialSet.circle.{u} ◁ f) (PointedSimplicialSet.circle.{u} ◁ g) := by
  exact H.map (PointedSimplicialSet.circle.{u} ◁ p) (suspensionHom T E) (suspensionHom T B)
    (PointedSimplicialSet.circle.{u} ◁ f) (PointedSimplicialSet.circle.{u} ◁ g)
    (familyVertex_suspension f) (familyVertex_suspension g)
    (RawSpectrumMapping.suspensionHom_post_pointed T p).symm
    ((familyVertex_suspension (f ≫ p)).trans
      (congrArg familyVertex (whiskerLeft_comp PointedSimplicialSet.circle.{u} f p)))

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

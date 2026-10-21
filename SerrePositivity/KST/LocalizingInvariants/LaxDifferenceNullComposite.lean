module

public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyZeroTriangle
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceUnitD

/-!
概要：元の lax 矢印と元の cofiber 射の合成は h Fun で零である。
方針：関手圏内の零角四角形の二辺を元の二つの代表に端点ごと比較する。
規約：各対象での零性ではなく自然変換全体の等式。使われ方：実随伴単位の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 端点も含む二辺の表示変更は、合成の零性を保つ。 -/
lemma comp_zero_of_arrowMk_eq {T : Type*} [Category T] [HasZeroMorphisms T]
    {x y z x' y' z' : T} (f : x ⟶ y) (g : y ⟶ z) (f' : x' ⟶ y') (g' : y' ⟶ z')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g')
    (h : f ≫ g = 0) : f' ≫ g' = 0 := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  obtain ⟨_, hz, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst x' y' z'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  rw [← hf, ← hg]
  exact h

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
local instance laxDifferenceFunctorZero (A X : SSet.{u}) [Quasicategory X] [HasZeroVertex X] :
    HasZeroVertex ((ihom A).obj X) := functorHasZeroVertex A X

local instance laxDifferenceFunctorZeroMorphisms (A X : SSet.{u})
    [Quasicategory X] [HasZeroVertex X] :
    HasZeroMorphisms ((ihom A).obj X).HomotopyCategory :=
  hasZeroMorphisms_ho

/-- 元の指定矢印族の h Fun の類。 -/
def laxArrowHom : FunctorHom ((laxFst p q).hom ≫ p.hom) ((laxSnd p q).hom ≫ q.hom) :=
  Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (laxArrowHomotopy p q))

lemma laxDifferenceNullComposite : laxArrowHom p q ≫ laxDifferenceProjectionHom p q =
    (0 : FunctorHom ((laxFst p q).hom ≫ p.hom) (laxDifference p q)) := by
  let a := F2.laxPullbackArrow p.hom q.hom
  let t := CofiberFamily.functorZeroTriangle E.obj a
  apply comp_zero_of_arrowMk_eq (squareHoBottom t.square) (squareHoRight t.square)
  · apply Truncated.HomotopyCategory.congr_arrowMk_homMk
    rw [squareBottomArrow_edge]
    change SSet.yonedaEquiv (squareBottomEdge ≫
      diagramFamilyTranspose (CofiberFamily.squares E.obj a)) = _
    rw [diagramFamilyTranspose_pre, CofiberFamily.squares_bottom]
    rfl
  · apply Truncated.HomotopyCategory.congr_arrowMk_homMk
    rw [squareRightArrow_edge]
    change SSet.yonedaEquiv (squareRightEdge ≫
      diagramFamilyTranspose (CofiberFamily.squares E.obj a)) = _
    rw [diagramFamilyTranspose_pre]
    have he : CofiberFamily.squares E.obj a ≫ (pre squareRightEdge).app E.obj =
        CofiberDiagrams.lift E.obj a ≫ CofiberDiagrams.right E.obj := by
      rw [CofiberDiagrams.right, ← Category.assoc, CofiberDiagrams.lift_inclusion]
    rw [he]
    rfl
  · exact CofiberFamily.functorZeroTriangle_comp_zero E.obj a

/-- 可逆な実余単位で相殺すると、D 成分を q で写した射との合成も零になる。 -/
lemma laxDifferenceUnitD_nullComposite {v : E.obj ⟶ D.obj}
    (a : QCatAdjunction q.hom v) (hv : IsFullyFaithful v) :
    laxArrowHom p q ≫
        (hoFunctor.map ((ihom (laxCategory p q).obj).map q.hom)).toFunctor.map
          (laxDifferenceUnitD p q a) =
      (0 : FunctorHom ((laxFst p q).hom ≫ p.hom) (laxDifference p q ≫ v ≫ q.hom)) := by
  have := fullyFaithfulRightAdjunction_counitHom_isIso q v a hv
  let ε := (hoFunctor.map ((pre (laxDifference p q)).app E.obj)).toFunctor.map a.counitHom
  have : IsIso ε := inferInstance
  apply (cancel_mono ε).1
  rw [Category.assoc, laxDifferenceUnitD_counit, laxDifferenceNullComposite, zero_comp]

end SerrePositivity.KST.LocalizingInvariants

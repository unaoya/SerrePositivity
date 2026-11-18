module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationModelFiltered
public import SerrePositivity.AlgebraicGeometry.FinitePresentationModelColimit
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
概要：既存の有限表示模型と指定脚を、基底環の下の圏で保つ。
方針：同じSmallModelの代数構造射をUnderへ送り、忘却がfiltered余極限を反映することを使う。
規約：対象・脚・元の終点を変更せず、Noether仮定や新しい模型の選択を足さない。
使われ方：2iのM05〜M07、BM18 Proposition 4.8(1)の有限表示模型の組み立て。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画M05：同じ有限表示模型と元の脚をUnderに保つ。 -/
def finitePresentationModelUnderDiagram (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    FinitePresentationModelIndex A B ⥤ Under (CommRingCat.of A) := by
  let F : FinitePresentationModelCategory A B ⥤ Under (CommRingCat.of A) :=
    { obj := fun X ↦ Under.mk (CommRingCat.ofHom (algebraMap A X.obj.left.obj))
      map := fun f ↦ Under.homMk (CommRingCat.ofHom f.hom.left.hom.hom.toRingHom) (by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        exact f.hom.left.hom.hom.commutes)
      map_id := by intro X; ext : 1; rfl
      map_comp := by intro X Y Z f g; ext : 1; rfl }
  exact (equivSmallModel (FinitePresentationModelCategory A B)).inverse ⋙ F

/-- 計画M06：同じ有限表示模型と元の脚をUnderに保つ。 -/
def finitePresentationModelUnderCocone (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    Cocone (finitePresentationModelUnderDiagram A B) := by
  refine ⟨Under.mk (CommRingCat.ofHom (algebraMap A B)), ?_⟩
  refine { app := fun j ↦ ?_, naturality := ?_ }
  · refine Under.homMk ((finitePresentationModelSmallCocone A B).ι.app j) ?_
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact ((equivSmallModel (FinitePresentationModelCategory A B)).inverse.obj j).obj.hom.hom.commutes
  · intro j k f
    ext : 1
    exact (finitePresentationModelSmallCocone A B).ι.naturality f

/-- 計画M07：同じ有限表示模型と元の脚をUnderに保つ。 -/
def finitePresentationModelUnderCoconeIsColimit (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    IsColimit (finitePresentationModelUnderCocone A B) := by
  letI : IsConnected (FinitePresentationModelIndex A B) := IsFiltered.isConnected (FinitePresentationModelIndex A B)
  apply isColimitOfReflects (Under.forget (CommRingCat.of A))
  exact finitePresentationModelSmallCoconeIsColimit A B

end SerrePositivity.AlgebraicGeometry.ArcRouteB

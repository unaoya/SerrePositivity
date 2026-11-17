module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelDiagram
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.CoverLaws

/-!
概要：同じ完全化した有限表示模型から、元の完全環への指定脚をまとめる。
方針：元の脚のFrobenius写像とH01の同型を合成し、同じ脚がarc被覆の細分になることを使う。
規約：元のA→BとSmallModelを保ち、模型の被覆判定の有限段への降下を仮定しない。
使われ方：2iのM09・M11、BM18 Proposition 4.8(1)。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画M09：指定された元の脚を完全化し、元の完全環へ戻す余錐。 -/
def perfectedModelCocone (p : ℕ) [Fact p.Prime]
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [PerfectRing A p] [PerfectRing B p] (hp : (p : A) = 0) :
    Cocone (perfectedModelDiagram p A B hp) := by
  let D := finitePresentationModelUnderDiagram A B
  let c := finitePresentationModelUnderCocone A B
  let hz (j : FinitePresentationModelIndex A B) : (p : (D.obj j).right) = 0 := by
    rw [← map_natCast (D.obj j).hom.hom, hp, map_zero]
  let hB : (p : B) = 0 := by rw [← map_natCast (algebraMap A B), hp, map_zero]
  refine ⟨Under.mk (CommRingCat.ofHom (algebraMap A B)), ?_⟩
  refine { app := fun j ↦ ?_, naturality := ?_ }
  · refine Under.homMk (CommRingCat.ofHom
      (frobeniusDirectLimitDesc p (hz j) hB (c.ι.app j).right.hom)) ?_
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change frobeniusDirectLimitDesc p (hz j) hB (c.ι.app j).right.hom
      (frobeniusDirectLimitOf (D.obj j).right p (Fact.out : p.Prime) (hz j) 0
        ((D.obj j).hom.hom a)) = algebraMap A B a
    rw [show frobeniusDirectLimitDesc p (hz j) hB (c.ι.app j).right.hom
        (frobeniusDirectLimitOf (D.obj j).right p (Fact.out : p.Prime) (hz j) 0
          ((D.obj j).hom.hom a)) = (c.ι.app j).right.hom ((D.obj j).hom.hom a) from
      RingHom.congr_fun (frobeniusDirectLimitDesc_comp_of_zero p (hz j) hB
        (c.ι.app j).right.hom) ((D.obj j).hom.hom a)]
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Under.w (c.ι.app j))) a
  · intro j k f
    ext : 1
    apply CommRingCat.hom_ext
    have hfoot := congrArg (fun u ↦ u.right.hom) (c.w f)
    change ((c.ι.app k).right.hom).comp (D.map f).right.hom =
      (c.ι.app j).right.hom at hfoot
    change (frobeniusDirectLimitDesc p (hz k) hB (c.ι.app k).right.hom).comp
      (frobeniusDirectLimitMap p (Fact.out : p.Prime) (hz j) (hz k) (D.map f).right.hom) =
        frobeniusDirectLimitDesc p (hz j) hB (c.ι.app j).right.hom
    dsimp only [frobeniusDirectLimitDesc]
    rw [RingHom.comp_assoc, frobeniusDirectLimitMap_comp, hfoot]

/-- 計画M11：元のBへ向かう同じ余錐の脚は、arc被覆の細分を与える。 -/
theorem perfectedModel_isArcHom (p : ℕ) [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [PerfectRing A p] [PerfectRing B p] (hp : (p : A) = 0)
    (hf : IsArcHom (algebraMap A B)) (j : FinitePresentationModelIndex A B) :
    IsArcHom ((perfectedModelDiagram p A B hp).obj j).hom.hom := by
  exact isArcHom_of_refinement _ (algebraMap A B)
    ((perfectedModelCocone p A B hp).ι.app j).right.hom
    (congrArg CommRingCat.Hom.hom (Under.w ((perfectedModelCocone p A B hp).ι.app j))) hf

end SerrePositivity.AlgebraicGeometry.ArcRouteB

module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessPullbackFunctor
public import SerrePositivity.InfinityCategories.F1.TransportWitnessColimitReflection

/-!
概要：底上の余極限に沿う実際の表現空間の降下。
方針：四角形を余極限へ貼り合わせ、余極限の脚による全頂点の被覆で表現条件を反映する。
規約：全高次の分類図式と全空間側の写像をともに厳密に保つ。
使われ方：pushout・非交和・骨格列の極限による表現空間の可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の余極限の各項で整合する実際の表現の族を全体へ貼り合わせる。
方針：四角形の極限の lift を取り、その全頂点の表現条件を各脚から反映する。
規約：族のパラメーターの全高次単体を保持する。
使われ方：表現空間の降下の極限の普遍射。 -/
def transportWitnessColimitLift {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
    {J : Type v} [Category.{w} J] [Small.{u + 1} J] {D : J ⥤ Over B}
    (c : Cocone D) (hc : IsColimit c)
    (s : Cone (D.op ⋙ transportWitnessPullbackFunctor p)) :
    s.pt ⟶ transportWitnessSpace ((transportPullbackArrowFunctor p).obj c.pt).hom := by
  let L := (transportPullbackSquareColimitCone_isLimit p c hc).lift
    (transportWitnessConeToSquare p s)
  refine fullSubcomplexLift (IsTransportWitnessVertex _) L ?_
  intro x
  let : LeftFibration ((transportPullbackArrowFunctor p).mapCocone c).pt.hom :=
    transportPullbackArrowFunctor_leftFibration p c.pt
  let : ∀ j, LeftFibration ((D ⋙ transportPullbackArrowFunctor p).obj j).hom :=
    fun j ↦ transportPullbackArrowFunctor_leftFibration p (D.obj j)
  apply isTransportWitnessVertex_of_colimit ((transportPullbackArrowFunctor p).mapCocone c)
    (isColimitOfPreserves (Over.forget B) hc)
    (fun j ↦ transportPullbackArrowFunctor_isPullback p (c.ι.app j))
  intro j
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x)
    ((transportPullbackSquareColimitCone_isLimit p c hc).fac
      (transportWitnessConeToSquare p s) (Opposite.op j))
  change (transportSquarePre ((transportPullbackArrowFunctor p).map (c.ι.app j))).app _
      (L.app _ x) = (s.π.app (Opposite.op j) |>.app _ x).val at h
  change IsTransportWitnessVertex ((transportPullbackArrowFunctor p).obj (D.obj j)).hom
    ((transportSquarePre ((transportPullbackArrowFunctor p).map (c.ι.app j))).app _ (L.app _ x))
  rw [h]
  exact fullSubcomplexOnVertices_vertex (s.π.app (Opposite.op j) |>.app _ x)

/-- 概要：貼り合わせた表現を四角形空間へ含めると四角形の極限の lift。
方針：全部分複体への lift の包含公式。
規約：全高次単体の厳密な等式。
使われ方：表現の降下の脚公式と一意性。 -/
lemma transportWitnessColimitLift_ι {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
    {J : Type v} [Category.{w} J] [Small.{u + 1} J] {D : J ⥤ Over B}
    (c : Cocone D) (hc : IsColimit c)
    (s : Cone (D.op ⋙ transportWitnessPullbackFunctor p)) :
    transportWitnessColimitLift p c hc s ≫
        transportWitnessSpaceι ((transportPullbackArrowFunctor p).obj c.pt).hom =
      (transportPullbackSquareColimitCone_isLimit p c hc).lift
        (transportWitnessConeToSquare p s) := by
  dsimp only [transportWitnessColimitLift]
  exact fullSubcomplexLift_ι _ _ _

/-- 概要：底上の余極限の各項への実際の表現の制限錐は極限。
方針：表現の貼り合わせの存在と四角形の極限による一意性を束ねる。
規約：単射性は不要で、分類図式と全空間側の写像を全高次で保持する。
使われ方：Kerodon Theorem 5.6.8.3 のセル貼り合わせと骨格列の降下。 -/
def transportWitnessColimitCone_isLimit {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
    {J : Type v} [Category.{w} J] [Small.{u + 1} J] {D : J ⥤ Over B}
    (c : Cocone D) (hc : IsColimit c) : IsLimit (transportWitnessColimitCone p c) where
  lift s := transportWitnessColimitLift p c hc s
  fac s j := by
    change transportWitnessColimitLift p c hc s ≫
      transportWitnessPre ((transportPullbackArrowFunctor p).map (c.ι.app j.unop))
        (transportPullbackArrowFunctor_isPullback p (c.ι.app j.unop)) = s.π.app j
    apply (cancel_mono (transportWitnessSpaceι
      ((transportPullbackArrowFunctor p).obj (D.obj j.unop)).hom)).1
    rw [Category.assoc, transportWitnessPre_ι, ← Category.assoc, transportWitnessColimitLift_ι]
    exact (transportPullbackSquareColimitCone_isLimit p c hc).fac
      (transportWitnessConeToSquare p s) j
  uniq s m hm := by
    apply (cancel_mono (transportWitnessSpaceι
      ((transportPullbackArrowFunctor p).obj c.pt).hom)).1
    rw [transportWitnessColimitLift_ι]
    apply (transportPullbackSquareColimitCone_isLimit p c hc).uniq
      (transportWitnessConeToSquare p s)
    intro j
    change (m ≫ transportWitnessSpaceι ((transportPullbackArrowFunctor p).obj c.pt).hom) ≫
        transportSquarePre ((transportPullbackArrowFunctor p).map (c.ι.app j.unop)) =
      s.π.app j ≫ transportWitnessSpaceι ((transportPullbackArrowFunctor p).obj (D.obj j.unop)).hom
    have h : (m ≫ transportWitnessPre ((transportPullbackArrowFunctor p).map (c.ι.app j.unop))
        (transportPullbackArrowFunctor_isPullback p (c.ι.app j.unop))) ≫
        transportWitnessSpaceι ((transportPullbackArrowFunctor p).obj (D.obj j.unop)).hom =
        s.π.app j ≫ transportWitnessSpaceι
          ((transportPullbackArrowFunctor p).obj (D.obj j.unop)).hom :=
      congrArg (fun f ↦ f ≫ transportWitnessSpaceι
        ((transportPullbackArrowFunctor p).obj (D.obj j.unop)).hom) (hm j)
    rw [Category.assoc, transportWitnessPre_ι] at h
    dsimp only [Cocone.op] at h
    simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories

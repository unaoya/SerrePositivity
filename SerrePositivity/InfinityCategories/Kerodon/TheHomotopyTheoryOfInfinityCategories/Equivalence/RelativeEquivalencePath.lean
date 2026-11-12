module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration

/-!
概要：射に対する相対的な可逆 path の持ち上げ写像。
方針：標的の可逆 path と指定された始点の引き戻しを取り、可逆 path の射を比較する。
規約：制限の持ち上げには始域の単射性と標的の quasicategory 性だけを課す。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の同値な図式の貼り合わせ。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：標的の可逆 path とその始点上の指定された点の組の単体集合。
方針：可逆 path の始点評価を射 p に沿って引き戻す。
規約：元の二つの単体集合は任意。
使われ方：Kerodon §4.5.3（Tag 032Y） の相対 path の持ち上げ。 -/
noncomputable def relativeEquivalencePathTarget {E B : SSet.{u}} (p : E ⟶ B) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p

/-- 概要：可逆 path をその像と始点の組に写す相対 path の写像。
方針：path の射と始点評価を引き戻しへ組にする。
規約：持ち上げ性は定義に含めない。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の制限の持ち上げ。 -/
noncomputable def relativeEquivalencePathMap {E B : SSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath E ⟶ relativeEquivalencePathTarget p :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint p 0)

/-- 概要：相対 path の写像の第一成分は元の path の像。
方針：引き戻しへの lift の第一射影の計算を使う。
規約：任意の射 p。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆 path の像の固定。 -/
lemma relativeEquivalencePathMap_fst {E B : SSet.{u}} (p : E ⟶ B) :
    relativeEquivalencePathMap p ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap p := pullback.lift_fst _ _ _

/-- 概要：相対 path の写像の第二成分は元の始点。
方針：引き戻しへの lift の第二射影の計算を使う。
規約：任意の射 p。
使われ方：Kerodon §4.5.3（Tag 032Y） の始点を固定した持ち上げ。 -/
lemma relativeEquivalencePathMap_snd {E B : SSet.{u}} (p : E ⟶ B) :
    relativeEquivalencePathMap p ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 0 := pullback.lift_snd _ _ _

/-- 概要：単射に沿う関手の制限は全単射に対して相対的な可逆 path を持ち上げる。
方針：可逆 path と内部 Hom の交換で、単射と始点評価の相対内部 Hom に移す。
規約：i は単射、X は quasicategory。A、B の quasicategory 性は不要。
使われ方：Kerodon §4.5.5（Tag 01F6） の categorical pushout の貼り合わせ。 -/
lemma trivialKanFibration_relativeEquivalencePathMap_pre {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeEquivalencePathMap ((pre i).app X)) := by
  let p := (pre i).app X
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0)
  have hsq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq.π :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) sq
  have hpb : IsPullback
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj X) 0) p ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso A X).hom)
      (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj X) 0) p)
      ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0)) p := by
    exact (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj X) 0) p).of_iso
      (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso A X) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by
        simpa only [Iso.refl_hom, Category.comp_id] using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso_endpoint A X 0).symm)
      (by simp)
  let eT : relativeEquivalencePathTarget p ≅ sq.pt := hpb.isoPullback
  have hw : relativeEquivalencePathMap p ≫ eT.hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso B X).hom ≫ sq.π := by
    apply sq.hom_ext
    · change (relativeEquivalencePathMap p ≫ hpb.isoPullback.hom) ≫
        pullback.fst ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0)) p = _
      rw [Category.assoc, hpb.isoPullback_hom_fst, ← Category.assoc,
        relativeEquivalencePathMap_fst, Category.assoc, sq.π_fst]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso_pre i
    · change (relativeEquivalencePathMap p ≫ hpb.isoPullback.hom) ≫
        pullback.snd ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0)) p = _
      rw [Category.assoc, hpb.isoPullback_hom_snd, relativeEquivalencePathMap_snd,
        Category.assoc, sq.π_snd]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso_endpoint B X 0).symm
  let e : Arrow.mk (relativeEquivalencePathMap p) ≅ Arrow.mk sq.π :=
    Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso B X) eT hw.symm
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.arrow_mk_iso_iff e).mpr hsq.mem⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

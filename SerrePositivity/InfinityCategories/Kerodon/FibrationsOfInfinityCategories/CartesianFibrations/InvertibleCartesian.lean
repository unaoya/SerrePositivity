module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：inner fibration に関する可逆辺の cartesian・cocartesian 性。
方針：可逆な端の辺を指定した相対的な外側ホーン充填を適用する。
規約：始域と標的は quasicategory とする。
使われ方：Kerodon Proposition 5.1.1.9（Tag 01TB）、Example 5.2.2.5（Tag 019P） の恒等 transport。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：inner fibration の始域の可逆辺は cartesian。
方針：可逆な最後の辺を持つ相対外側ホーンを充填する。
規約：辺の可逆性は始域のホモトピー圏で判定する。
使われ方：Kerodon Proposition 5.1.1.9（Tag 01TB） の (1) から (2)。 -/
@[kerodon 01TB, kerodon 01TC]
lemma isCartesianEdge_of_isInvertibleEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B] (p : X ⟶ B) [InnerFibration p] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e.edge := by
  intro n a b ha sq
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr ha).mpr he
  obtain ⟨F, hF, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_finalHorn p n a b sq.w h
  exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFp }

/-- 概要：inner fibration の始域の可逆辺は cocartesian。
方針：可逆な最初の辺を持つ相対外側ホーンを充填する。
規約：辺の可逆性は始域のホモトピー圏で判定する。
使われ方：Kerodon Proposition 5.1.1.9（Tag 01TB） の (1) から (3)。 -/
lemma isCocartesianEdge_of_isInvertibleEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B] (p : X ⟶ B) [InnerFibration p] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e.edge := by
  intro n a b ha sq
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr ha).mpr he
  obtain ⟨F, hF, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_initialHorn p n a b sq.w h
  exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFp }

/-- 概要：inner fibration に関して恒等辺は cocartesian。
方針：恒等射の可逆性と可逆辺の相対的充填を使う。
規約：恒等辺は頂点 x の定値一単体として表す。
使われ方：Kerodon Example 5.2.2.5（Tag 019P）、恒等 transport の証人。 -/
@[kerodon 01TC]
lemma isCocartesianEdge_constant {X B : SSet.{u}} [Quasicategory X] [Quasicategory B]
    (p : X ⟶ B) [InnerFibration p] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  exact isCocartesianEdge_of_isInvertibleEdge p _ hi

/-- 概要：cartesian 辺の像が可逆なら元の辺も可逆。
方針：底の外側ホーンを可逆辺で充填し、その上で相対充填を行う。
規約：この逆向きには始域の quasicategory 性や p の inner fibration 性は不要。
使われ方：Kerodon Proposition 5.1.1.9（Tag 01TB） の逆向き。 -/
lemma isInvertibleEdge_of_isCartesianEdge {X B : SSet.{u}} [Quasicategory B]
    (p : X ⟶ B) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e.edge)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map p))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers e
  intro n a ha
  have hmap : (a ≫ p).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) =
      (e.map ((truncation 2).map p)).edge := by
    change p.app (Opposite.op ⦋1⦌) (a.app (Opposite.op ⦋1⦌) _) = _
    rw [ha]
    rfl
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge _ hp n (a ≫ p) hmap
  have sq : CommSq a (horn (n + 2) (Fin.last (n + 2))).ι p b := ⟨hb.symm⟩
  have := he n a b ha sq
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：可逆辺は、cartesian で底の像が可逆な辺と同値。
方針：可逆辺の相対充填と、底の可逆性による可逆性の検出を組み合わせる。
規約：p は quasicategory 間の inner fibration。
使われ方：Kerodon Proposition 5.1.1.9（Tag 01TB）、fiber 内の可逆性の判定。 -/
@[kerodon 01T8, kerodon 01TB]
lemma isInvertibleEdge_iff_isCartesianEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B] (p : X ⟶ B) [InnerFibration p] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map p)) :=
  ⟨fun he ↦ ⟨isCartesianEdge_of_isInvertibleEdge p e he, he.map p⟩,
    fun h ↦ isInvertibleEdge_of_isCartesianEdge p e h.1 h.2⟩

/-- 概要：cocartesian 辺の像が可逆なら元の辺も可逆。
方針：底の外側ホーンを可逆辺で充填し、その上で相対充填を行う。
規約：始域と底は quasicategory とし、p の inner fibration 性は不要。
使われ方：Kerodon Proposition 5.1.1.9（Tag 01TB） の逆向き。 -/
lemma isInvertibleEdge_of_isCocartesianEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B]
    (p : X ⟶ B) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e.edge)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map p))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_of_hasInitialHornFillers e
  intro n a ha
  have hmap : (a ≫ p).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) =
      (e.map ((truncation 2).map p)).edge := by
    change p.app (Opposite.op ⦋1⦌) (a.app (Opposite.op ⦋1⦌) _) = _
    rw [ha]
    rfl
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge _ hp n (a ≫ p) hmap
  have sq : CommSq a (horn (n + 2) 0).ι p b := ⟨hb.symm⟩
  have := he n a b ha sq
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：可逆辺は、cocartesian で底の像が可逆な辺と同値。
方針：可逆辺の相対充填と、底の可逆性による可逆性の検出を組み合わせる。
規約：p は quasicategory 間の inner fibration。
使われ方：Kerodon Proposition 5.1.1.9（Tag 01TB）、fiber 内の可逆性の判定。 -/
@[kerodon 01TB]
lemma isInvertibleEdge_iff_isCocartesianEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B] (p : X ⟶ B) [InnerFibration p] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map p)) :=
  ⟨fun he ↦ ⟨isCocartesianEdge_of_isInvertibleEdge p e he, he.map p⟩,
    fun h ↦ isInvertibleEdge_of_isCocartesianEdge p e h.1 h.2⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

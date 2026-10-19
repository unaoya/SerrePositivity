module
public import SerrePositivity.InfinityCategories.Derived.CofiberSquareComparisonData
public import SerrePositivity.InfinityCategories.Derived.FullHomotopyLift

/-! # Semifree 内の suspension 四角形の比較ホモトピー

概要：前合成・後合成から作った四角形の射を Semifree 内の実際のホモトピーに戻す。
方針：周囲の関手圏の射を辺で代表し、全頂点が Semifree であることから円柱全体を持ち上げる。
規約：始点・終点成分の同定は後続。使われ方：D7 の suspension の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S]

/-- Semifree の標準 suspension 四角形の包含像は明示的な複体四角形。 -/
lemma semifreeSuspensionSquare_inclusion (X : Semifree S) :
    (semifreeSuspensionSquare X).square ≫ derivedInfinityInclusion =
      (suspensionComplexSquareData X).square :=
  (semifreeCofiberSquare_inclusion (0 : X.val ⟶ 0) (0 : X.val ⟶ 0)
    X.property (complexSemifree_zero S) (complexSemifree_zero S)).trans
      (cofiberComplexSquareData_square _ _).symm

/-- 包含した四角形を端点とする、周囲の suspension 比較の射。 -/
def suspensionComplexSquareHomOnInclusion {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk
        (functorVertex ((semifreeSuspensionSquare X).square ≫ derivedInfinityInclusion)) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (dgNerve S (Complex S)))) ⟶
        SSet.HomotopyCategory.mk
          (functorVertex ((semifreeSuspensionSquare Y).square ≫ derivedInfinityInclusion)) := by
  have h := suspensionComplexSquareHom a
  rw [← semifreeSuspensionSquare_inclusion X, ← semifreeSuspensionSquare_inclusion Y] at h
  exact h

/-- 周囲の suspension 比較の射を表す実際の辺。 -/
def suspensionComplexSquareEdge {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (dgNerve S (Complex S))))
      (functorVertex ((semifreeSuspensionSquare X).square ≫ derivedInfinityInclusion))
      (functorVertex ((semifreeSuspensionSquare Y).square ≫ derivedInfinityInclusion)) :=
  Classical.choose (homotopyCategory_homMk_surjective _ _ (suspensionComplexSquareHomOnInclusion a))

/-- 選んだ比較辺の類は前合成と後合成から作った射。 -/
lemma suspensionComplexSquareEdge_homMk {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    SSet.Truncated.HomotopyCategory.homMk (suspensionComplexSquareEdge a) =
      suspensionComplexSquareHomOnInclusion a :=
  Classical.choose_spec
    (homotopyCategory_homMk_surjective _ _ (suspensionComplexSquareHomOnInclusion a))

/-- 全複体の dg nerve における四角形比較の実際のホモトピー代表。 -/
def suspensionComplexSquareHomotopy {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    SSet.Homotopy ((semifreeSuspensionSquare X).square ≫ derivedInfinityInclusion)
      ((semifreeSuspensionSquare Y).square ≫ derivedInfinityInclusion) :=
  simplicialHomotopyOfFunctorEdge (suspensionComplexSquareEdge a)

/-- Semifree 内の実際の suspension 四角形比較。 -/
def semifreeSuspensionSquareHomotopy {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    SSet.Homotopy (semifreeSuspensionSquare X).square (semifreeSuspensionSquare Y).square :=
  Classical.choose (exists_fullInclusion_homotopy S (Complex S) (complexSemifree S)
    (semifreeSuspensionSquare X).square (semifreeSuspensionSquare Y).square
    (suspensionComplexSquareHomotopy a))

/-- 持ち上げた suspension 比較の包含像は元の周囲の比較。 -/
lemma semifreeSuspensionSquareHomotopy_inclusion {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    (semifreeSuspensionSquareHomotopy a).h ≫ derivedInfinityInclusion =
      (suspensionComplexSquareHomotopy a).h :=
  Classical.choose_spec (exists_fullInclusion_homotopy S (Complex S) (complexSemifree S)
    (semifreeSuspensionSquare X).square (semifreeSuspensionSquare Y).square
    (suspensionComplexSquareHomotopy a))

/-- Semifree の suspension 四角形全体のホモトピー圏の射。 -/
def semifreeSuspensionSquareHom {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk (functorVertex (semifreeSuspensionSquare X).square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (derivedInfinityCategory S))) ⟶
        SSet.HomotopyCategory.mk (functorVertex (semifreeSuspensionSquare Y).square) :=
  SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (semifreeSuspensionSquareHomotopy a))

end SerrePositivity.InfinityCategories

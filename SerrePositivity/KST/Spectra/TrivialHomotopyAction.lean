module

public import SerrePositivity.KST.Spectra.GroupCochainHomotopyFunctions
public import SerrePositivity.KST.Spectra.GroupCoefficientCochainFunctor

/-!
概要：自明な点つき Kan 作用の π_* の誘導作用の自明性と cochain の係数への比較。
方針：恒等点つき射の誘導写像が恒等であることを作用の同型に束ねる。
規約：群の有限性や係数の有理性は不要。
使われ方：Goerss–Jardine I §7、VIII §2。自明作用の π_* の cochain の線形係数への移送。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.PointedActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : Type u) [Group G] (X : PointedSimplicialSet.{u}) [KanComplex X.right]

local instance trivialHomotopyActionUnderlyingKan : KanComplex (Action.trivial G X).V.right :=
  inferInstanceAs (KanComplex X.right)

lemma homotopyAction_trivial_ρ (k : ℕ) (g : G)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right k X.basepoint) :
    ((homotopyAction (Action.trivial G X) k).ρ g).asHom a = a := by
  change pointedHomotopyMap (k + 1) (𝟙 X) a = a
  exact pointedHomotopyMap_id X (k + 1) a

/-- 概要：自明な点つき作用の π_* の作用は自明な群作用と同型。
方針：基礎の群を恒等同型で対応させ、誘導作用の恒等性を使う。
規約：k は実際の次数 k+1。
使われ方：Goerss–Jardine VIII §2。非斉次 cochain の係数を自明作用へ移す。 -/
def homotopyTrivialIso (k : ℕ) : homotopyAction (Action.trivial G X) k ≅
    Action.trivial G (GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right k X.basepoint)) :=
  Action.mkIso (Iso.refl _) (fun g ↦ by
    ext a
    exact homotopyAction_trivial_ρ G X k g a)

/-- 概要：自明な Kan 作用の π_* の cochain は自明な係数作用の非斉次 cochain と自然に同型。
方針：cochain の π_* の自然同型に誘導作用の自明性の同型を合成する。
規約：群の圏の余単体図式の実際の同型。
使われ方：Goerss–Jardine VIII §2。線形な自明係数の cochain と比較する出発点。 -/
def trivialHomotopyFunctionNatIso (k : ℕ) :
    KanHomotopyGroup.diagram (obj (Action.trivial G X)) k ≅
      GroupCoefficientCochains.obj
        (Action.trivial G (GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right k X.basepoint))) :=
  homotopyFunctionNatIso (Action.trivial G X) k ≪≫
    (GroupCoefficientCochains.functor G).mapIso (homotopyTrivialIso G X k)

end

end SerrePositivity.KST.Spectra.PointedActionCochains

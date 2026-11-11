module

public import SerrePositivity.KST.Spectra.TrivialHomotopyAction
public import SerrePositivity.KST.Spectra.AdditiveFunctionEquiv
public import SerrePositivity.KST.Spectra.CommutativeHomotopyDiagram
public import SerrePositivity.KST.Spectra.RepresentationCochainComparison

/-!
概要：自明な Kan 作用の高次 π_* の加法的 cochain 図式と線形な自明係数 cochain の比較。
方針：誘導作用の自明性の比較に乗法群から加法群の座標変換を施す。
規約：係数の高次 π_* に指定した加群構造を仮定する。Tot のホモトピー群の主張は含まない。
使われ方：Goerss–Jardine VIII §2。有理係数の cochain 消滅を高次 π_* の複体へ接続する。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.TrivialHomotopyCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : PointedSimplicialSet.{u}) [KanComplex X.right]

/-- 概要：標準基点の二以上の次数の π_* を加法的可換群とする。
方針：乗法的なホモトピー群へ Additive を施す。
規約：q は実際の次数 q+2。
使われ方：Goerss–Jardine I §7、VIII §2。線形 cochain の指定する係数。 -/
abbrev coefficient (q : ℕ) := Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right (q + 1) X.basepoint)

variable (R G : Type u) [CommRing R] [Group G]

local instance trivialLinearUnderlyingKan : KanComplex (Action.trivial G X).V.right :=
  inferInstanceAs (KanComplex X.right)

/-- 概要：指定した加群構造の高次 π_* を自明係数とする線形 cochain の図式。
方針：自明表現を加群の圏の作用へ送り、線形な非斉次 cochain を適用する。
規約：q は実際の次数 q+2。
使われ方：Goerss–Jardine VIII §2。群 cohomology による高次 π_* の cochain の計算。 -/
def linearDiagram (q : ℕ) [Module R (coefficient X q)] :
    CosimplicialObject (ModuleCat.{u} R) :=
  LinearGroupCochains.obj ((Rep.RepToAction R G).obj (Rep.trivial R G (coefficient X q)))

/-- 概要：自明な Kan 作用の高次 π_* の加法的 cochain は指定した線形係数の cochain と同型。
方針：群の cochain の自然同型と関数群の加法的表示を各次数で合成する。
規約：環 R の加群構造を係数に指定し、比較では加法群へ忘却する。
使われ方：Goerss–Jardine VIII §2。有理線形 cochain と元の π_* の余単体構造の橋渡し。 -/
def linearDiagramIso (q : ℕ) [Module R (coefficient X q)] :
    KanHomotopyGroup.additiveDiagram (PointedActionCochains.obj (Action.trivial G X)) q ≅
      linearDiagram X R G q ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  let e := PointedActionCochains.trivialHomotopyFunctionNatIso G X (q + 1)
  NatIso.ofComponents
    (fun n ↦ AddEquiv.toAddCommGrpIso
      (X := (KanHomotopyGroup.additiveDiagram
        (PointedActionCochains.obj (Action.trivial G X)) q).obj n)
      (Y := (linearDiagram X R G q ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj n)
      ((MulEquiv.toAdditive (e.app n).groupIsoToMulEquiv).trans
        (additiveFunctionEquiv (Fin n.len → G)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right (q + 1) X.basepoint))))
    (fun f ↦ by
      ext a
      funext s
      have h := congr($(e.hom.naturality f) (Additive.toMul a) s)
      exact congrArg Additive.ofMul h)

end

end SerrePositivity.KST.Spectra.TrivialHomotopyCochains

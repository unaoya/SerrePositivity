module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 実際の収縮による終対象との局所化比較

概要：一点への実際の区間収縮から終射の局所化可逆性を証明し、二つの可縮対象の比較へ使う。
方針：選んだ頂点への定数射を終射の逆にする。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13 の正則 bar と path space の比較。
使われ方：全空間の比較の局所化可逆性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel
open scoped Simplicial

/--
概要：選んだ頂点への実際の収縮を持つ単体集合の終射は局所化同型。
方針：終対象から選んだ頂点への定数写像を逆とし、区間ホモトピーを局所化へ送る。
規約：単体集合の Kan 性は不要。
使われ方：正則 bar の可縮性の局所化での表示。
-/
theorem contractedSpace_terminal_localized_isIso (X : SSet.{u}) (z : X.obj (Opposite.op ⦋0⦌))
    (H : SSet.Homotopy (SSet.const z) (𝟙 X)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from X)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let e : Q.obj X ≅ Q.obj (⊤_ SSet.{u}) :=
    { hom := Q.map (terminal.from X)
      inv := Q.map (SSet.const (X := ⊤_ SSet.{u}) z)
      hom_inv_id := by
        rw [← Q.map_comp, SSet.comp_const]
        exact (AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts Q SSet.anodyneExtensions) H).trans (Q.map_id X)
      inv_hom_id := by
        rw [← Q.map_comp]
        have h : SSet.const (X := ⊤_ SSet.{u}) z ≫ terminal.from X = 𝟙 _ :=
          terminalIsTerminal.hom_ext _ _
        rw [h, Q.map_id] }
  exact e.isIso_hom

/--
概要：終射が局所化同型である二対象の間の任意の射も局所化同型。
方針：終対象への射の一意性と合成の二対三を使う。
規約：射が収縮と厳密に可換である必要はない。
使われ方：正則 bar から基点始点 path space への比較。
-/
theorem map_between_contractible_localized_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from X)))
    (hY : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from Y))) :
    IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  have h : f ≫ terminal.from Y = terminal.from X := terminalIsTerminal.hom_ext _ _
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map f ≫
      AnodyneHomotopy.anodyneQ.map (terminal.from Y)) := by
    rw [← Functor.map_comp, h]
    exact hX
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.Comparison

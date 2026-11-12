module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryFaces
public import SerrePositivity.KST.Spectra.AnodyneMappingLifts
public import SerrePositivity.KST.Spectra.PathSpace

/-!
概要：単射への RLP による全ての面を指定した単体の充填。
方針：互換な面を境界へ貼り、境界の単射に沿って持ち上げる。
規約：終対象への射の右持ち上げ性を明示する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。零次数の連結写像の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

/-- 概要：path space の終対象への射は全ての単射に対して RLP を持つ。
方針：区間の始点包含の anodyne 性を点つき Hom の指数版充填へ移す。
規約：標的 Y は Kan。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3（Tag 00TJ）。三角形の全境界充填。 -/
theorem basedPathSpace_terminal_rlp (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from (basedPathSpace Y).right) :=
  basedHom_terminal_rlp_monomorphisms _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y pointedInterval_basepoint_anodyne

namespace BoundaryFaces

/-- 概要：終対象への射が単射に RLP を持つ単体集合では互換な全ての面を充填できる。
方針：面を境界へ貼り合わせ、境界の単射を持ち上げる。
規約：単体の次元は n + 2。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。零次数の連結射の単射性。 -/
theorem exists_filler {X : SSet.{u}}
    (hX : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from X))
    {n : ℕ} {f : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ X)} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.IsCompatible f) :
    ∃ q : (Δ[n + 2] : SSet.{u}) ⟶ X, ∀ j, stdSimplex.δ j ≫ q = f j := by
  let : HasLiftingProperty (boundary.{u} (n + 2)).ι (terminal.from X) := hX _ inferInstance
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.desc hf) (boundary.{u} (n + 2)).ι (terminal.from X)
      (terminal.from (Δ[n + 2] : SSet.{u})) := ⟨Subsingleton.elim _ _⟩
  refine ⟨sq.lift, fun j ↦ ?_⟩
  rw [← boundary.ι_ι_assoc, sq.fac_left]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ι_desc hf j

end BoundaryFaces

end SerrePositivity.KST.Spectra

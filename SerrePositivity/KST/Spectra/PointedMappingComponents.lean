module

public import SerrePositivity.KST.Spectra.PointedMappingHomotopy
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyComponents

/-!
概要：点つき写像空間の連結成分の等式と基点固定ホモトピーの存在の同値。
方針：Kan な写像空間で π₀ の等式を単一の辺へ戻し、相対 curry で変換する。
規約：源の Kan 性は不要。標的が Kan であることを使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面の写像空間の π₀ の計算。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 複体で同じ連結成分に属する二つの頂点は単一の辺で結ばれる。
方針：零次数の類の同値と RelStruct の存在を合成する。
規約：辺は v から w の向き。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。写像空間の同じ成分の代表を比較する。 -/
theorem nonempty_edge_of_piZero_eq {Z : SSet.{u}} [KanComplex Z] {v w : Z _⦋0⦌}
    (h : π₀.mk v = π₀.mk w) : Nonempty (Z.Edge v w) := by
  let fv : Z.PtSimplex 0 v := (PtSimplex.equiv₀ v).symm v
  let fw : Z.PtSimplex 0 v := (PtSimplex.equiv₀ v).symm w
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk fw = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk fv := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.injective
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_mk, fv, fw, Equiv.apply_symm_apply] using h.symm
  obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopyZero.mk_eq_iff fw fv).1 hz
  have e := PtSimplex.RelStruct₀.equiv₀ r
  exact ⟨by simpa only [fv, fw, Equiv.apply_symm_apply] using e⟩

namespace PointedMapping

/-- 概要：点つき内部 Hom で同じ成分を表す射は、基点固定でホモトピック。
方針：Kan な内部 Hom の成分の等式を辺へ戻し、逆向きはホモトピーの curry の辺を取る。
規約：頂点は familyVertex のパラメータ族の表示。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。写像空間と球面の類の比較。 -/
theorem piZero_eq_iff_pointedHomotopy {X Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (f g : X ⟶ Y) :
    π₀.mk (familyVertex f) = π₀.mk (familyVertex g) ↔
      ∃ H : SSet.Homotopy f.right g.right,
        X.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
          toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom := by
  constructor
  · intro h
    obtain ⟨e⟩ := nonempty_edge_of_piZero_eq h
    exact ⟨homotopyOfEdge e, homotopyOfEdge_base e⟩
  · rintro ⟨H, hH⟩
    exact π₀.sound (edgeOfHomotopy H hH)

end PointedMapping

end

end SerrePositivity.KST.Spectra

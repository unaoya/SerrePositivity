module

public import SerrePositivity.KST.Spectra.AdjacentFacePrismFaces
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyInvariance

/-!
概要：隣接二面による RelStruct から、境界を固定する実際の区間ホモトピーを構成する。
方針：隣接面の prism を後合成し、各境界面の制限で相対条件を検査する。
規約：第二の面から第一の面への向き。Kan 性は構成自体に不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面の写像空間の連結成分との比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Opposite
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：RelStruct の prism は元の単体の各境界面上で基点に定数。
方針：境界面が切り替え位置の前・後・一致かで分け、定数面か共通境界へ移す。
規約：元の単体の次元は n+1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。相対ホモトピーの境界条件。 -/
theorem relStruct_prism_face {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    {f g : X.PtSimplex (n + 1) x} {i : Fin (n + 2)} (r : PtSimplex.RelStruct f g i)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ▷ (Δ[1] : SSet.{u}) ≫ (AdjacentFacePrism.map i ≫ r.map) = SSet.const x := by
  rcases lt_trichotomy j i with hji | hji | hij
  · rw [← Category.assoc, AdjacentFacePrism.face_of_lt i j hji, Category.assoc,
      r.δ_map_of_lt j.castSucc (by simpa only [Fin.castSucc_lt_castSucc_iff] using hji),
      SSet.comp_const]
  · subst j
    rw [← Category.assoc, AdjacentFacePrism.face_self, Category.assoc, Category.assoc,
      r.δ_succ_map, PtSimplex.δ_map, SSet.comp_const]
  · rw [← Category.assoc, AdjacentFacePrism.face_of_gt i j hij, Category.assoc,
      r.δ_map_of_gt j.succ (by simpa only [Fin.succ_lt_succ_iff] using hij), SSet.comp_const]

/-- 概要：一つの RelStruct を境界固定の区間ホモトピーへ変換する。
方針：prism を充填単体へ後合成し、境界単体を各面へ因子分解して定数条件を示す。
規約：g から f の向き。零次元では境界が空。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。商の関係の実際の球面ホモトピーとしての実現。 -/
def relStructHomotopy {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    {f g : X.PtSimplex n x} {i : Fin (n + 1)} (r : PtSimplex.RelStruct f g i) : g.Homotopy f where
  h := AdjacentFacePrism.map i ≫ r.map
  h₀ := by rw [← Category.assoc, AdjacentFacePrism.zero, r.δ_succ_map]
  h₁ := by rw [← Category.assoc, AdjacentFacePrism.one, r.δ_castSucc_map]
  rel := by
    simp only [Subcomplex.ofSimplex_ι, SSet.comp_const]
    cases n with
    | zero =>
      ext m ⟨⟨s, hs⟩, t⟩
      simp at hs
    | succ n =>
      apply NatTrans.ext
      funext ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      rintro ⟨⟨s, hs⟩, t⟩
      simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
        Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff] at hs
      obtain ⟨j, ⟨v, rfl⟩⟩ := hs
      exact congrArg (fun k : (Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ X ↦
        k.app _ (stdSimplex.objEquiv.{u}.symm v, t))
        (relStruct_prism_face r j)

/-- 概要：正次数のホモトピー類の等式は境界固定の実際のホモトピーの存在と同値。
方針：RelStruct の存在へ戻して prism へ移し、逆向きは実装済みのホモトピー不変性を使う。
規約：向きのため関係の二つの代表を交換する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面の写像空間の π₀ の計算。 -/
theorem KanHomotopyGroup.mk_eq_iff_relativeHomotopy {X : SSet.{u}} [KanComplex X]
    {n : ℕ} {x : X _⦋0⦌} (f g : X.PtSimplex (n + 1) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g ↔ Nonempty (f.Homotopy g) := by
  constructor
  · intro h
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct (n + 1) g f 0).1 h.symm
    exact ⟨relStructHomotopy r⟩
  · rintro ⟨H⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.eq_of_relativeHomotopy H

end

end SerrePositivity.KST.Spectra

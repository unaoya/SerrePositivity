module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace
public import Mathlib.Algebra.Group.Action.Basic

/-!
概要：球面的境界の充填の存在を交代和の零性で判定する。
方針：最後のホーンを充填し、交代和で最後の面の類を同定して代表を変更する。
規約：各面の次数は二以上。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な障害類を実際の単体の存在へ戻す。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SphericalBoundary
end SerrePositivity.KST.Spectra.SphericalBoundary
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries


noncomputable section

variable {X : SSet.{u}} [KanComplex X] {n : ℕ} {x : X _⦋0⦌}

/-- 概要：任意の球面的な面の族は最後の面を変更すれば充填できる。
方針：指定した最後以外の面をホーンへ貼り、欠ける面を境界定数単体として取る。
規約：最初の n + 3 面を厳密に保持する。
使われ方：Goerss–Jardine I §7。最後の面に集約した充填の障害。 -/
theorem exists_horn_boundary (a : Fin (n + 4) → X.PtSimplex (n + 2) x) :
    ∃ b : X.PtSimplex (n + 2) x,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary (Function.update a (Fin.last (n + 3)) b)) := by
  let α (j : Fin (n + 4)) (_ : j ≠ Fin.last (n + 3)) : (Δ[n + 2] : SSet.{u}) ⟶ X :=
    (a j).map
  have hα : horn.IsCompatible α := fun _ _ _ _ _ ↦ by simp [α]
  let b : X.PtSimplex (n + 2) x :=
    { map := stdSimplex.δ (Fin.last (n + 3)) ≫ hα.liftOfKanComplex
      comm := by
        ext j : 1
        simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
        rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
          hα.δ_liftOfKanComplex _ (Fin.castSucc_ne_last j)]
        exact PtSimplex.δ_map _ _ }
  refine ⟨b, ⟨{map := hα.liftOfKanComplex, face_eq := ?_}⟩⟩
  intro j
  by_cases hj : j = Fin.last (n + 3)
  · subst j; simp only [Function.update_self]; rfl
  · rw [hα.δ_liftOfKanComplex j hj, Function.update_of_ne hj]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (exists_horn_boundary)


/-- 概要：最後の面だけを変えた二つの族の交代和が同じなら、その面の類は同じ。
方針：共通の先頭部分の和を打ち消し、最後の符号が整数の単元であることを使う。
規約：他の面の代表は厳密に同じ。
使われ方：Goerss–Jardine I §7。ホーンの最後の面の障害の同定。 -/
theorem additiveClass_last_of_update (a : Fin (n + 4) → X.PtSimplex (n + 2) x)
    (b : X.PtSimplex (n + 2) x)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass (Function.update a (Fin.last (n + 3)) b) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (a (Fin.last (n + 3))) := by
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass (Function.update a (Fin.last (n + 3)) b) =
      (∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (a j.castSucc)) +
        (-1 : ℤ) ^ (n + 3) • _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass b := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass
    rw [Fin.sum_univ_castSucc]
    simp
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass a =
      (∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (a j.castSucc)) +
        (-1 : ℤ) ^ (n + 3) • _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (a (Fin.last (n + 3))) :=
    Fin.sum_univ_castSucc _
  rw [hu, ha] at h
  exact ((isUnit_neg_one : IsUnit (-1 : ℤ)).pow (n + 3)).smul_left_cancel.mp
    (add_left_cancel h)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (additiveClass_last_of_update)


/-- 概要：球面的境界の交代和が零なら指定した全ての面を持つ単体が存在する。
方針：最後のホーンを充填し、交代境界関係で最後の面の類を同定し、比較ホーンで直す。
規約：標的の Kan 性と実際の次数が二以上であることだけを使う。
使われ方：Goerss–Jardine I §7、VIII §1。cochain の障害の消滅からの実充填。 -/
theorem exists_of_alternatingClass_eq_zero
    (a : Fin (n + 4) → X.PtSimplex (n + 2) x) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass a = 0) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a) := by
  obtain ⟨b, ⟨T⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_horn_boundary a
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (a (Fin.last (n + 3))) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.additiveClass_last_of_update a b ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass_eq_zero T).trans h.symm)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a (Fin.last (n + 3))) :=
    congrArg Additive.toMul hb
  have he' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk ((Function.update a (Fin.last (n + 3)) b)
      (Fin.last (n + 3))) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a (Fin.last (n + 3))) := by
    simpa only [Function.update_self] using he
  simpa only [Function.update_idem, Function.update_eq_self] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryLastFace.exists_replace T he')

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (exists_of_alternatingClass_eq_zero)


/-- 概要：球面的境界が充填できることと、そのホモトピー類の交代和の零性は同値。
方針：充填からは交代境界関係、逆向きは最後の面を直す Kan 充填を使う。
規約：存在は通常の単体的な射の存在。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な障害の厳密な判定。 -/
theorem nonempty_iff_alternatingClass_eq_zero
    (a : Fin (n + 4) → X.PtSimplex (n + 2) x) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary a) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass a = 0 :=
  ⟨fun ⟨T⟩ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass_eq_zero T, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_of_alternatingClass_eq_zero a⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (nonempty_iff_alternatingClass_eq_zero)


end

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.additiveClass_last_of_update := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.additiveClass_last_of_update

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.exists_horn_boundary := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_horn_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.exists_of_alternatingClass_eq_zero := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_of_alternatingClass_eq_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.nonempty_iff_alternatingClass_eq_zero := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.nonempty_iff_alternatingClass_eq_zero

module

public import SerrePositivity.InfinityCategories.F1B.KanFunctorTranspose
public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeBoundaryExistence

/-!
概要：境界上の普遍余錐から、指定された境界余錐の像を持つ相対余錐を構成する。
方針：余錐の族を境界固定で延長し、二変数を転置する。
規約：境界余錐の最初の頂点だけに通常の余極限性を要求する。
使われ方：関手の境界制限上の大域的な相対 Kan 図式の局所入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：境界を固定した関手圏に値を取る指定図式には相対普遍余錐が存在する。
方針：境界を固定する余錐の族を延長し、その転置を指定図式上の余錐として読む。
規約：境界上の最初の余錐だけが余極限なら十分。
使われ方：写像空間の境界充填を大域的に組み立てるための各 fiber の相対余錐の存在。 -/
lemma exists_kanBoundaryRelativeCocone_of_first_colimit {J D : SSet.{u}}
    [Quasicategory D] (n : ℕ)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom J).obj D)
    (ha : a ≫ coconeRestriction J D = (boundary (n + 1)).ι ≫ d)
    (hfirst : IsColimitCone (kanCoconeFamilyAt a
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩)) :
    ∃ z : JoinCocone (kanFunctorTranspose d),
      KanRelativeCoconeLifting ((pre (boundary (n + 1)).ι).app D) z ∧
        z.val ≫ (pre (boundary (n + 1)).ι).app D = kanFunctorTranspose a := by
  obtain ⟨f, hfA, hfd, hf⟩ := exists_kanCocone_boundary_extension_of_first_colimit n a d ha hfirst
  have hdiagram : joinInl J (Δ[0] : SSet.{u}) ≫ kanFunctorTranspose f = kanFunctorTranspose d := by
    rw [← kanFunctorTranspose_pre_right]
    change kanFunctorTranspose (f ≫ coconeRestriction J D) = kanFunctorTranspose d
    rw [hfd]
  refine ⟨⟨kanFunctorTranspose f, hdiagram⟩, hf, ?_⟩
  change kanFunctorTranspose f ≫ (pre (boundary (n + 1)).ι).app D = kanFunctorTranspose a
  rw [← kanFunctorTranspose_pre_left, hfA]

end SerrePositivity.InfinityCategories.F1B

module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeBoundaryTarget
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeBoundaryExistence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeCriterion

/-!
概要：標的の余錐も固定する境界相対関手上の標準相対余極限の存在。
方針：最初の境界頂点の U 余極限性から余錐の族を延長し、転置する。
規約：指定部分・元の図式・U による像をすべて厳密に保つ。
使われ方：相対 Kan 図式の境界延長の各 fiber の局所入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：最初の境界余錐が U 余極限なら、相対境界関手上の標準相対余極限が存在する。
方針：操作的な相対余錐の延長と普遍性を、転置後の標準相対余極限へ移す。
規約：U は inner fibration、境界以外の全標的余錐も指定する。
使われ方：全図式の境界を埋めるための相対内部 Hom 上の局所余錐の供給。 -/
lemma exists_kanBoundaryRelativeColimit_of_first_relativeColimit {J D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U] (n : ℕ)
    (sj : internalHom.PullbackObjObj (boundary (n + 1)).ι U)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom J).obj D)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj E)
    (h : d ≫ (ihom J).map U = g ≫ coconeRestriction J E)
    (ha : a ≫ coconeRestriction J D = (boundary (n + 1)).ι ≫ d)
    (hg : a ≫ (ihom (join J (Δ[0] : SSet.{u}))).map U = (boundary (n + 1)).ι ≫ g)
    (hfirst : IsRelativeColimitCone U (kanCoconeFamilyAt a
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩)) :
    ∃ z : JoinCocone (SerrePositivity.InfinityCategories.F1B.functorTranspose d), IsRelativeColimitCone sj.π z ∧
      z.val ≫ (pre (boundary (n + 1)).ι).app D = SerrePositivity.InfinityCategories.F1B.functorTranspose a ∧
        z.val ≫ (ihom (Δ[n + 1] : SSet.{u})).map U = SerrePositivity.InfinityCategories.F1B.functorTranspose g := by
  have : Quasicategory ((internalHom.obj (Opposite.op (Δ[n + 1] : SSet.{u}))).obj D) :=
    inferInstanceAs (Quasicategory ((ihom (Δ[n + 1] : SSet.{u})).obj D))
  have : Quasicategory sj.pt := kanRelativeInternalHomTarget_quasicategory U _ sj
  obtain ⟨f, hfA, hfp, hf⟩ := exists_kanRelativeCocone_boundary_extension U n sj a d g h ha hg
    (kanRelativeCoconeLifting_of_isRelativeColimitCone U _ hfirst)
  have hfd : f ≫ coconeRestriction J D = d := by
    have he := congrArg (fun k ↦ k ≫
      pullback.fst ((ihom J).map U) (coconeRestriction J E)) hfp
    simpa only [Category.assoc, kanRelativeCoconeRestriction_fst, pullback.lift_fst] using he
  have hfg : f ≫ (ihom (join J (Δ[0] : SSet.{u}))).map U = g := by
    have he := congrArg (fun k ↦ k ≫
      pullback.snd ((ihom J).map U) (coconeRestriction J E)) hfp
    simpa only [Category.assoc, kanRelativeCoconeRestriction_snd, pullback.lift_snd] using he
  have hdiagram : joinInl J (Δ[0] : SSet.{u}) ≫ SerrePositivity.InfinityCategories.F1B.functorTranspose f =
      SerrePositivity.InfinityCategories.F1B.functorTranspose d := by
    rw [← SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right]
    change SerrePositivity.InfinityCategories.F1B.functorTranspose (f ≫ coconeRestriction J D) = _
    rw [hfd]
  let z : JoinCocone (SerrePositivity.InfinityCategories.F1B.functorTranspose d) := ⟨SerrePositivity.InfinityCategories.F1B.functorTranspose f, hdiagram⟩
  refine ⟨z, kanIsRelativeColimitCone_of_lifting sj.π z hf, ?_, ?_⟩
  · change SerrePositivity.InfinityCategories.F1B.functorTranspose f ≫ (pre (boundary (n + 1)).ι).app D = _
    rw [← SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left, hfA]
  · change SerrePositivity.InfinityCategories.F1B.functorTranspose f ≫ (ihom (Δ[n + 1] : SSet.{u})).map U = _
    rw [← kanFunctorTranspose_postcomp, hfg]

end SerrePositivity.InfinityCategories.F1B

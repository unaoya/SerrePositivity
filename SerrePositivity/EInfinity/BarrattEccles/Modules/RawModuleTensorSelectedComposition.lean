module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedAtMaxImage
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition

/-!
概要：選択 cochain と元の終端尾の閉射の実合成を、同じ普遍成分へ回収する。
方針：元の dg 合成を Hom 後合成へ戻し、符号作用と元の実像の式を使う。
規約：同じ閉射・次数・符号を保つ。使われ方：cone の最後に残る切断合成の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_compose {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℤˣ) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).val
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) (add_zero k) =
    r • (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk := by
  rw [modulePostcompose_graded A (dgAlgebraCategory A ((assocForget A).obj X)) ((strictRawModuleProbeFunctor A X).obj P)]
  have hs : (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) =
    r • (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) := by
    simp only [Units.smul_def, map_zsmul]
  exact hs.trans (congrArg (fun v => r • v)
    (strictRawModuleTensorElementSelectedCochainAtMax_image A X P Q c J k hJ hk))

end SerrePositivity.EInfinity.BarrattEccles

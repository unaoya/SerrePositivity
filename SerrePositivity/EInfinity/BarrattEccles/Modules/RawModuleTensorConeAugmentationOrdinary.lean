module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeAugmentationAt
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeOrdinaryClosed
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition

/-!
概要：元の cone の通常辺と同じ終端 augmentation の実合成は、始点 augmentation である。
方針：同じ閉 frame 辺を回収し、元の自然変換の自然性と閉 cochain の合成式を使う。
規約：元の実辺と全端点を保つ。使われ方：二重 cone の通常三点方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits

open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationAt_compose_ordinary_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk) (add_zero 0) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c a)).val := by
  induction a using Fin.cases with
  | zero => exact False.elim (ha0 rfl)
  | succ i =>
    have hab : i.succ < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
    induction b using Fin.cases with
    | zero => exact False.elim (Fin.not_lt_zero _ hab)
    | succ j =>
        have hij : i ≤ j := Fin.succ_le_succ_iff.mp hab.le
        let f := (strictRawModuleTensorElementDiagram A X P Q).map (c.map (homOfLE hij))
        let g := (strictRawModuleTensorElementAugmentation A X P Q).app (c.obj j)
        let h := (strictRawModuleTensorElementAugmentation A X P Q).app (c.obj i)
        have hnat : f ≫ g = h := by
          exact ((strictRawModuleTensorElementAugmentation A X P Q).naturality
            (c.map (homOfLE hij))).trans (Category.comp_id _)
        have hg := strictRawModuleTensorConeData_hom_ordinary_closed A X P Q c I i.succ j.succ
          hI ha hb hk (Fin.succ_ne_zero _) hab.le
        change HEq ((strictRawModuleTensorConeData A X P Q c).hom I i.succ j.succ 0 hI ha hb hk)
          (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ f).val at hg
        change compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ g).val
          ((strictRawModuleTensorConeData A X P Q c).hom I i.succ j.succ 0 hI ha hb hk) (add_zero 0) =
          (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ h).val
        have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp f g).symm
        have hn := congrArg (fun q : (strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i) ⟶
            (strictRawModuleProbeFunctor A X).obj P =>
          (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ q).val) hnat
        have he := congrArg (fun v : GradedHom A
            (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i)))
            (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj j))) 0 =>
          compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ g).val
            v (add_zero 0)) (eq_of_heq hg)
        exact he.trans (hc.trans hn)

end SerrePositivity.EInfinity.BarrattEccles

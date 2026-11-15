module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementPinched

/-!
# 全要素列の同じ普遍 cochain と全微分方程式

概要：M10 の元の実 pinched 単体を同じ全次数の線形成分へ送る。
方針：既存の線形同型と全再添字・任意 Hom 鎖写像の成分式を適用する。
規約：HA Construction 1.3.1.6、全有限部分集合・単射と非単射を保持する。
使われ方：元の全係数 cone の削除・合成・退化の方程式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ全 pinched 単体の元の線形 cochain 表示。
方針：既存の同じ全線形表示を適用する。
規約：HA 1.3.1.6、全次数。使われ方：元の cone の実高次成分。 -/
def strictRawModuleTensorElementLinear {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    LinearSimplex A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))) n :=
  PinchedHom.toLinearSimplex (strictRawModuleTensorElementPinchedSimplex A X P Q c)

/-- 概要：同じ全 cochain は全有限部分集合の微分方程式を満たす。
方針：元の線形単体の検証済み全方程式を評価する。
規約：HA 1.3.1.6、正しい次数。使われ方：全 cone 方程式の元の削除項。 -/
lemma strictRawModuleTensorElementLinear_equation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential A ((strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk) =
      (strictRawModuleTensorElementLinear A X P Q c).val.rhs J k hk :=
  (strictRawModuleTensorElementLinear A X P Q c).equation J k hJ hk

/-- 概要：同じ全線形族は元の全再添字・終端射の作用と整合する。
方針：同じ pinched 単体の再添字式を同じ線形表示へ送る。
規約：HA 1.3.1.6、終端を変える全作用素。使われ方：高次成分の貼り合わせ。 -/
lemma strictRawModuleTensorElementLinear_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    LinearSimplex.pullback θ.toOrderHom (strictRawModuleTensorElementLinear A X P Q c) =
    pinchedLinearSimplexMap
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))
      (strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) := by
  have h := congrArg (PinchedHom.toLinearSimplex (A := A)
    (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
    (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
    (y := ForgetEnrichment.to (Complex A)
      ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))))
    (strictRawModuleTensorElementPinchedSimplex_reindex A X P Q c θ)
  exact (toLinearSimplex_pullback (strictRawModuleTensorElementPinchedSimplex A X P Q c) θ).symm.trans
    (h.trans (pinchedHomChainMapSimplex_linear _ _))

/-- 概要：同じ全 cochain の任意の成分の再添字式。
方針：同じ全線形再添字式を元の部分集合で評価する。
規約：HA 1.3.1.6、同じ終端射。使われ方：全削除項と退化の式。 -/
lemma strictRawModuleTensorElementLinear_component_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) =
    LinearData.component (pullback θ.toOrderHom
      (strictRawModuleTensorElementLinear A X P Q c).val) J k hJ hk := by
  exact (congrArg (fun s : LinearSimplex A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))) m =>
      s.val.component J k hJ hk)
    (strictRawModuleTensorElementLinear_reindex A X P Q c θ)).symm

/-- 概要：同じ cochain の単射再添字は元の像部分集合の成分。
方針：既存の同じ単射 pullback 成分式を使う。
規約：HA 1.3.1.6、同じ像。使われ方：選択した cochain の回収。 -/
lemma strictRawModuleTensorElementLinear_component_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component (J.image θ.toOrderHom) k
      (hJ.image θ.toOrderHom) (by rw [Finset.card_image_of_injOn hi]; exact hk) :=
  (strictRawModuleTensorElementLinear_component_reindex A X P Q c θ J k hJ hk).trans
    (pullback_component_of_inj θ.toOrderHom
      (strictRawModuleTensorElementLinear A X P Q c).val J k hJ hk hi)

/-- 概要：同じ cochain の非単射再添字成分は零。
方針：既存の同じ非単射 pullback 成分式を使う。
規約：HA 1.3.1.6、同じ退化。使われ方：全 cone の退化成分の消滅。 -/
lemma strictRawModuleTensorElementLinear_component_not_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : ¬ Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) = 0 :=
  (strictRawModuleTensorElementLinear_component_reindex A X P Q c θ J k hJ hk).trans
    (pullback_component_of_not_inj θ.toOrderHom
      (strictRawModuleTensorElementLinear A X P Q c).val J k hJ hk hi)

end SerrePositivity.EInfinity.BarrattEccles

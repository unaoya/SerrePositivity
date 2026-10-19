module

public import SerrePositivity.InfinityCategories.F1.RelativeBoundaryFamilyFiber

/-!
概要：動く底と境界を持つ全 lift の前合成比較の fiber ごとの同値性。
方針：各パラメーターのデータを関手で表し、厳密な fiber 同型で固定境界の比較へ移す。
規約：パラメーターの各頂点だけでなく fiber 空間全体の同値を示す。
使われ方：分類図式の族全体の円柱比較の同値判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：前合成同値による動く境界固定 lift の比較は各パラメーター fiber で同値。
方針：二つの厳密な fiber 同型が固定境界比較と可換することを確認する。
規約：i の単射性は要求せず j と j≫i の単射性だけを使う。
使われ方：分類図式を動かしたまま比較を同値にする主要入力。 -/
lemma relativeBoundaryFamilyPre_fiber_isQCatEquivalence
    {A D C E B L : SSet.{u}} [Quasicategory B]
    (i : D ⟶ A) (hi : IsPrecompositionEquivalence i) (j : C ⟶ D)
    [Mono j] [Mono (j ≫ i)] (p : E ⟶ B) [LeftFibration p]
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p)
    (d : L ⟶ rA.pt) (l : L _⦋0⦌) :
    IsQCatEquivalence (vertexFiberMap (relativeBoundaryFamilyProjection rA d)
      (relativeBoundaryFamilyProjection rD (d ≫ relativeBoundaryDataPre i j p rA rD))
      (relativeBoundaryFamilyPre i j p rA rD d)
      (relativeBoundaryFamilyPre_projection i j p rA rD d) l) := by
  obtain ⟨a, v, hv, hz₀, hz₁⟩ := exists_relativeHomBoundaryVertex (j ≫ i) p rA (d.app _ l)
  have hvD : v ≫ p = j ≫ (i ≫ a) := by simpa only [Category.assoc] using hv
  have hD₀ : rD.fst.app _ ((d ≫ relativeBoundaryDataPre i j p rA rD).app _ l) =
      functorVertex v := by
    have h := congrArg (fun w ↦ w.app (Opposite.op ⦋0⦌) (d.app _ l))
      (relativeBoundaryDataPre_fst i j p rA rD)
    exact h.trans hz₀
  have hD₁ : rD.snd.app _ ((d ≫ relativeBoundaryDataPre i j p rA rD).app _ l) =
      functorVertex (i ≫ a) := by
    have h := congrArg (fun w ↦ w.app (Opposite.op ⦋0⦌) (d.app _ l))
      (relativeBoundaryDataPre_snd i j p rA rD)
    change rD.snd.app _ ((d ≫ relativeBoundaryDataPre i j p rA rD).app _ l) =
      ((pre i).app B).app _ (rA.snd.app _ (d.app _ l)) at h
    rw [hz₁] at h
    exact h
  let eA := relativeBoundaryFamilyStrictFiberIso (j ≫ i) p rA d l a v hv hz₀ hz₁
  let eD := relativeBoundaryFamilyStrictFiberIso j p rD
    (d ≫ relativeBoundaryDataPre i j p rA rD) l (i ≫ a) v hvD hD₀ hD₁
  let k := vertexFiberMap (relativeFunctorPre p a (j ≫ i)) (relativeFunctorPre p (i ≫ a) j)
    (relativeFunctorPre p a i) (relativeFunctorPre_comp p a i j)
    (relativeFunctorVertex p ((j ≫ i) ≫ a) v hv)
  let F := vertexFiberMap (relativeBoundaryFamilyProjection rA d)
    (relativeBoundaryFamilyProjection rD (d ≫ relativeBoundaryDataPre i j p rA rD))
    (relativeBoundaryFamilyPre i j p rA rD d)
    (relativeBoundaryFamilyPre_projection i j p rA rD d) l
  have heA := relativeBoundaryFamilyStrictFiberIso_hom_ι (j ≫ i) p rA d l a v hv hz₀ hz₁
  have heD := relativeBoundaryFamilyStrictFiberIso_hom_ι j p rD
    (d ≫ relativeBoundaryDataPre i j p rA rD) l (i ≫ a) v hvD hD₀ hD₁
  have hkι : k ≫ vertexFiberι (relativeFunctorPre p (i ≫ a) j)
        (relativeFunctorVertex p (j ≫ (i ≫ a)) v hvD) =
      vertexFiberι (relativeFunctorPre p a (j ≫ i))
        (relativeFunctorVertex p ((j ≫ i) ≫ a) v hv) ≫ relativeFunctorPre p a i :=
    vertexFiberMap_ι _ _ _ _ _
  have hcomm : F ≫ eD.hom = eA.hom ≫ k := by
    apply vertexFiber_hom_ext (relativeFunctorPre p (i ≫ a) j)
      (relativeFunctorVertex p (j ≫ (i ≫ a)) v hvD)
    apply vertexFiber_hom_ext ((ihom D).map p) (functorVertex (i ≫ a))
    simp only [Category.assoc]
    rw [heD, ← Category.assoc, vertexFiberMap_ι, Category.assoc,
      relativeBoundaryFamilyPre_curry]
    change _ = eA.hom ≫ k ≫ _ ≫ _
    rw [← Category.assoc k, hkι]
    simp only [Category.assoc]
    rw [relativeFunctorPre_ι p a i]
    simpa only [Category.assoc] using congrArg (fun w ↦ w ≫ (pre i).app E) heA.symm
  have hk : IsQCatEquivalence k := relativeFunctorBoundaryMap_isQCatEquivalence p a i hi j _
  have hcomp : IsQCatEquivalence (F ≫ eD.hom) := by
    rw [hcomm]
    exact (qCatEquivalenceOfIso eA).isQCatEquivalence.comp hk
  exact (qCatEquivalenceOfIso eD).isQCatEquivalence.cancel_right hcomp

/-- 概要：quasicategory のパラメーター空間上で動く底と境界の比較は空間全体で同値。
方針：パラメーター射影の left fibration 性と全 fiber の比較を合わせる。
規約：固定図式の同値だけでなく実際の族全体の射について結論する。
使われ方：両端固定の区間写像空間上の輸送円柱比較。 -/
lemma relativeBoundaryFamilyPre_isQCatEquivalence
    {A D C E B L : SSet.{u}} [Quasicategory B] [Quasicategory L]
    (i : D ⟶ A) (hi : IsPrecompositionEquivalence i) (j : C ⟶ D)
    [Mono j] [Mono (j ≫ i)] (p : E ⟶ B) [LeftFibration p]
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p)
    (d : L ⟶ rA.pt) : IsQCatEquivalence (relativeBoundaryFamilyPre i j p rA rD d) := by
  let : Quasicategory (relativeBoundaryFamilySpace rA d) :=
    quasicategory_of_innerFibration (relativeBoundaryFamilyProjection rA d)
  let : Quasicategory (relativeBoundaryFamilySpace rD
      (d ≫ relativeBoundaryDataPre i j p rA rD)) :=
    quasicategory_of_innerFibration (relativeBoundaryFamilyProjection rD _)
  apply isQCatEquivalence_of_leftFibration_fibers
    (relativeBoundaryFamilyProjection rA d)
    (relativeBoundaryFamilyProjection rD (d ≫ relativeBoundaryDataPre i j p rA rD))
    (relativeBoundaryFamilyPre i j p rA rD d)
    (relativeBoundaryFamilyPre_projection i j p rA rD d)
  exact relativeBoundaryFamilyPre_fiber_isQCatEquivalence i hi j p rA rD d

end SerrePositivity.InfinityCategories

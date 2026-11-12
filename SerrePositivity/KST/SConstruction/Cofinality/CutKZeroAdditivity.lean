module
public import SerrePositivity.KST.SConstruction.CutStableComparison
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelDiagram

/-!
概要：元の切断 cofiber 正方形の三角圏 K₀ 関係を取り出す。
方針：同じ cofiber 頂点を零角つき三角形へ読み替え、三角形関係を適用する。
規約：切断の中央は元の恒等関手であり、cofiber の選択を変えない。
使われ方：障害余核図式の S 方向の加法的分解。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の cofiber 図式の対象類は三角圏 K₀ で加法的。
方針：元の四角形の零角と押し出し性から完全三角形を作る。
規約：三つの対象は元の評価射の値。
使われ方：元の切断比較の K₀ 関係。 -/
lemma cofiberKZero_vertex (X : StableModel.{u})
    (v : (cofiberDiagrams X.carrier) _⦋0⦌) :
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
        (HomotopyCategory.mk ((cofiberStableMiddle X).val.app _ v)) =
      TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
        (HomotopyCategory.mk ((cofiberStableSubobject X).val.app _ v)) +
      TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
        (HomotopyCategory.mk ((cofiberStableQuotient X).val.app _ v)) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X.carrier := ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val, hv.1⟩
  have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t := hv.2
  have h := TriangulatedK0.mk_triangle (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht)
    ⟨t, ht, ⟨Iso.refl _⟩⟩
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X.carrier).apply_symm_apply v.val
  change TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) 1 0)) =
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) 0 0)) +
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) 1 1)) at h
  change TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app _ v.val)) =
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app _ v.val)) +
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app _ v.val))
  rw [← he]
  have ev (x y : Fin 2) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex
    (Y := X.carrier) (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)
  exact (congrArg (fun a => TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
    (HomotopyCategory.mk a)) (ev 1 0)).trans (h.trans
      (congrArg₂ (fun a b =>
        TriangulatedK0.mk (C := hoFunctor.obj X.carrier) (HomotopyCategory.mk a) +
        TriangulatedK0.mk (C := hoFunctor.obj X.carrier) (HomotopyCategory.mk b))
        (ev 0 0).symm (ev 1 1).symm))

/-- 概要：元の切断の中央対象類は両端の対象類の和。
方針：切断比較が返す元の cofiber 頂点に加法関係を適用する。
規約：全ての切断位置を許し、同じ S_n 内の対象類を比較する。
使われ方：S 方向の余核 Segal 分解の生成元公式。 -/
lemma cutKZero_vertex (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sStableModel n X).carrier _⦋0⦌) :
    TriangulatedK0.mk (C := hoFunctor.obj (sStableModel n X).carrier)
        (HomotopyCategory.mk v) =
      TriangulatedK0.mk (C := hoFunctor.obj (sStableModel n X).carrier)
        (HomotopyCategory.mk (((cutStableComparison n k X ≫
          cofiberStableSubobject (sStableModel n X)).val).app _ v)) +
      TriangulatedK0.mk (C := hoFunctor.obj (sStableModel n X).carrier)
        (HomotopyCategory.mk (((cutStableComparison n k X ≫
          cofiberStableQuotient (sStableModel n X)).val).app _ v)) := by
  have h := cofiberKZero_vertex (sStableModel n X) ((cutStableComparison n k X).val.app _ v)
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg Subtype.val (cutStableComparison_middle n k X))
      (Opposite.op ⦋0⦌)) v
  change (cofiberStableMiddle (sStableModel n X)).val.app _
    ((cutStableComparison n k X).val.app _ v) = v at he
  exact (congrArg (fun a => TriangulatedK0.mk
    (C := hoFunctor.obj (sStableModel n X).carrier) (HomotopyCategory.mk a)) he).symm.trans h

/-- 概要：元の cofiber 三評価の K₀ 作用の加法関係。
方針：対象生成元に元の cofiber 正方形の関係を適用する。
規約：同じ三評価の準同型の等号。
使われ方：完全なパラメーター族への加法関係の移送。 -/
lemma cofiberKZero_map (X : StableModel.{u}) :
    triangulatedKZeroSourceMap (cofiberStableMiddle X) =
      triangulatedKZeroSourceMap (cofiberStableSubobject X) +
      triangulatedKZeroSourceMap (cofiberStableQuotient X) := by
  apply TriangulatedK0.hom_ext (C := hoFunctor.obj (cofiberStableModel X).carrier)
  intro a
  obtain ⟨v, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  change triangulatedKZeroSourceMap (cofiberStableMiddle X)
      (TriangulatedK0.mk (HomotopyCategory.mk v)) =
    triangulatedKZeroSourceMap (cofiberStableSubobject X)
      (TriangulatedK0.mk (HomotopyCategory.mk v)) +
    triangulatedKZeroSourceMap (cofiberStableQuotient X)
      (TriangulatedK0.mk (HomotopyCategory.mk v))
  rw [triangulatedKZeroSourceMap_mk, triangulatedKZeroSourceMap_mk,
    triangulatedKZeroSourceMap_mk]
  exact cofiberKZero_vertex X v

/-- 概要：切断の左右の射は K₀ 上で恒等写像を分解する。
方針：三つの評価の加法関係へ同じ切断比較を前合成する。
規約：同じ S_n 上の元の二つの射を使う。
使われ方：左右の区間制限の単射性を導く。 -/
lemma cutKZero_id (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    AddMonoidHom.id (TriangulatedK0 (hoFunctor.obj (sStableModel n X).carrier)) =
      triangulatedKZeroSourceMap (cutStableComparison n k X ≫
        cofiberStableSubobject (sStableModel n X)) +
      triangulatedKZeroSourceMap (cutStableComparison n k X ≫
        cofiberStableQuotient (sStableModel n X)) := by
  have h := congrArg (fun g => g.comp (triangulatedKZeroSourceMap
    (cutStableComparison n k X))) (cofiberKZero_map (sStableModel n X))
  rw [AddMonoidHom.add_comp] at h
  exact (triangulatedKZeroSourceMap_id (sStableModel n X)).symm.trans
    ((congrArg triangulatedKZeroSourceMap (cutStableComparison_middle n k X).symm).trans
      ((triangulatedKZeroSourceMap_comp _ _).trans
        (h.trans (congrArg₂ (· + ·) (triangulatedKZeroSourceMap_comp _ _).symm
          (triangulatedKZeroSourceMap_comp _ _).symm))))

end SerrePositivity.KST.SConstruction.Cofinality

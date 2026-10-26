module
public import SerrePositivity.KST.SConstruction.Cofinality.CutCokernelLaws
public import SerrePositivity.KST.SConstruction.EdgeSegalEvaluations

/-!
概要：元の指定 S_n 射の K₀ 余核を全連続辺の座標へ分解する。
方針：最初の辺と残りの区間への切断同型を帰納的に反復する。
規約：各座標は元の端点制限であることを別途照合する。
使われ方：障害余核の元の S 図式と bar の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：元の余核群の列を先頭と末尾から組み立てる加法同型。
方針：Fin.consEquiv の加法保存を点ごとに確認する。
規約：座標の順序を保持する。
使われ方：区間分解の反復の束ね直し。 -/
def cutCokernelConsEquiv (n : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    cutKZeroCokernel 1 f × (Fin n → cutKZeroCokernel 1 f) ≃+
      (Fin (n + 1) → cutKZeroCokernel 1 f) where
  toEquiv := Fin.consEquiv (fun _ => cutKZeroCokernel 1 f)
  map_add' a b := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- 概要：元の S_n K₀ 余核と n 個の一段余核との加法同型。
方針：切断直積同型と Fin.cons による列の復元を反復する。
規約：零段は元の S_0 余核の一意性を使う。
使われ方：元の障害図式の次数ごとの bar 座標。 -/
def cutCokernelEdgeEquiv {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (n : ℕ) → cutKZeroCokernel n f ≃+ (Fin n → cutKZeroCokernel 1 f)
  | 0 => by
    letI := cutKZeroCokernel_zero_subsingleton f
    letI : Unique (cutKZeroCokernel 0 f) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
    exact AddEquiv.ofUnique
  | n + 1 => (cutCokernelEquiv (n + 1) ⟨1, by omega⟩ f).trans
      (((AddEquiv.refl (cutKZeroCokernel 1 f)).prodCongr (cutCokernelEdgeEquiv f n)).trans
        (cutCokernelConsEquiv n f))

/-- 概要：最初の切断の左包含は最初の連続辺の包含。
方針：端点の値を計算する。
規約：全ての正の段数で成立する。
使われ方：反復分解の先頭座標の回収。 -/
lemma cutCokernel_firstInterval (n : ℕ) :
    cutLeftIntervalInclusion (n + 1) ⟨1, by omega⟩ =
      edgeIntervalInclusion (n + 1) ⟨0, by omega⟩ := by
  apply DFunLike.ext
  intro j
  apply Fin.ext
  exact (Nat.zero_add j.val).symm

/-- 概要：残りの区間の各連続辺は元の次の連続辺。
方針：二つの平行移動の合成を端点で計算する。
規約：元の区間包含そのものの等号。
使われ方：反復分解の末尾座標の回収。 -/
lemma cutCokernel_tailInterval (n : ℕ) (i : Fin n) :
    (cutRightIntervalInclusion (n + 1) ⟨1, by omega⟩).comp
      (edgeIntervalInclusion n i) = edgeIntervalInclusion (n + 1) i.succ := by
  apply DFunLike.ext
  intro j
  apply Fin.ext
  change i.val + j.val + 1 = i.val + 1 + j.val
  omega

/-- 概要：辺座標同型の各座標は元の端点制限を厳密に回収する。
方針：先頭の区間の等号と末尾の二重制限の合成則で帰納する。
規約：元の指定射の同じ余核上で計算する。
使われ方：面・退化の元の写像と bar 座標の照合。 -/
lemma cutCokernelEdgeEquiv_apply {X Y : StableModel.{u}} (f : X ⟶ Y)
    (n : ℕ) (a : cutKZeroCokernel n f) (i : Fin n) :
    cutCokernelEdgeEquiv f n a i = cutCokernelRestriction f (edgeIntervalInclusion n i) a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (cutCokernelEquiv (n + 1) ⟨1, by omega⟩ f a).1 = _
      exact (congrArg Prod.fst (cutCokernelEquiv_apply (n + 1) ⟨1, by omega⟩ f a)).trans
        (DFunLike.congr_fun (congrArg (cutCokernelRestriction f) (cutCokernel_firstInterval n)) a)
    · change cutCokernelEdgeEquiv f n (cutCokernelEquiv (n + 1) ⟨1, by omega⟩ f a).2 j = _
      have he := congrArg Prod.snd (cutCokernelEquiv_apply (n + 1) ⟨1, by omega⟩ f a)
      exact (ih _ j).trans ((congrArg
        (fun b => cutCokernelRestriction f (edgeIntervalInclusion n j) b) he).trans
          ((DFunLike.congr_fun (cutCokernelRestriction_comp f (edgeIntervalInclusion n j)
            (cutRightIntervalInclusion (n + 1) ⟨1, by omega⟩)) a).symm.trans
              (DFunLike.congr_fun (congrArg (cutCokernelRestriction f)
                (cutCokernel_tailInterval n j)) a)))

end SerrePositivity.KST.SConstruction.Cofinality

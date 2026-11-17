module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutIntervals

/-!
概要：二つの切れ目の間の射が、端点・恒等射・全合成を保持することを証明する。
方針：区間への包含との可換性と包含の単射性を使う。
規約：元の全単体の各射を用いる。使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの実関手。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：共通の射の表示は恒等射を保つ。
方針：四Homの恒等射と区間表示の恒等則を使う。
規約：空の自己Homも含む。使われ方：Riehl–Verity Proposition 3.1.10 の実因子。 -/
lemma walkingAdjunctionOrderHom_id (X Y : WalkingAdjunctionPoint) (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionOrderHom (𝟙 A) = OrderHom.id := by
  cases X <;> cases Y
  · exact augmentedOrderHom_id A
  · rfl
  · rfl
  · change ordinalIntervalMap (augmentedOrderHom (𝟙 A.unop)) = OrderHom.id
    rw [augmentedOrderHom_id, ordinalIntervalMap_id]

/-- 概要：共通の射の表示は全合成を保つ。
方針：四Homの合成則と区間表示の反変合成則を使う。
規約：元の射の順序を保つ。使われ方：Riehl–Verity Proposition 3.1.10 の実因子。 -/
lemma walkingAdjunctionOrderHom_comp {X Y : WalkingAdjunctionPoint}
    {A B C : walkingAdjunctionHom X Y} (f : A ⟶ B) (g : B ⟶ C) :
    walkingAdjunctionOrderHom (f ≫ g) =
      (walkingAdjunctionOrderHom g).comp (walkingAdjunctionOrderHom f) := by
  cases X <;> cases Y
  · exact augmentedOrderHom_comp f g
  · rfl
  · rfl
  · change ordinalIntervalMap (augmentedOrderHom (g.unop ≫ f.unop)) = _
    rw [augmentedOrderHom_comp, ordinalIntervalMap_comp]
    rfl

variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：二つの切れ目の間の区間の、元の全単体への実包含。
方針：検証済みの区間の範囲を使う。規約：全頂点を同時に扱う。
使われ方：Riehl–Verity Proposition 3.1.10 の制限した実射。 -/
def walkingAdjunctionCutIntervalInclusion (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) (i : Fin (n + 1)) :
    Fin (walkingAdjunctionCutIntervalSize a b i) →o
      Fin (walkingAdjunctionOrdinalCard X Y (F.obj i)) :=
  ordinalSegmentInclusion _ _ _ (walkingAdjunctionCutInterval_bound a b i (h i))

/-- 概要：区間の実包含は単射。
方針：始点の加法を相殺する。規約：空の区間も含む。
使われ方：Riehl–Verity Proposition 3.1.10 の制限した全合成の照合。 -/
lemma walkingAdjunctionCutIntervalInclusion_injective (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) (i : Fin (n + 1)) :
    Function.Injective (walkingAdjunctionCutIntervalInclusion a b h i) := by
  intro x y hxy
  apply Fin.ext
  have hv := congrArg Fin.val hxy
  change walkingAdjunctionCutCoordinate a i + x.val =
    walkingAdjunctionCutCoordinate a i + y.val at hv
  omega

/-- 概要：切れ目の間の射と実包含の正方形は可換。
方針：構成した区間制限の全点での可換性を使う。
規約：元の全単体の任意の射。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCutInterval_square (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (walkingAdjunctionCutIntervalInclusion a b h j).comp
        (walkingAdjunctionCutIntervalMap a b h hij) =
      (walkingAdjunctionOrderHom (F.map (homOfLE hij))).comp
        (walkingAdjunctionCutIntervalInclusion a b h i) :=
  ordinalRestrict_square _ _ _ _ _ _ _ _ _

/-- 概要：可換な正方形を全ての実点で評価する。
方針：射の等式を評価する。規約：同じ包含と元の射。
使われ方：Riehl–Verity Proposition 3.1.10 の端点と合成の照合。 -/
lemma walkingAdjunctionCutInterval_square_apply (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) (k : Fin (walkingAdjunctionCutIntervalSize a b i)) :
    walkingAdjunctionCutIntervalInclusion a b h j (walkingAdjunctionCutIntervalMap a b h hij k) =
      walkingAdjunctionOrderHom (F.map (homOfLE hij))
        (walkingAdjunctionCutIntervalInclusion a b h i k) :=
  congrArg (fun q : Fin (walkingAdjunctionCutIntervalSize a b i) →o
    Fin (walkingAdjunctionOrdinalCard X Y (F.obj j)) => q k)
      (walkingAdjunctionCutInterval_square a b h hij)

/-- 概要：切れ目の間の射は恒等射を保つ。
方針：単射な実包含へ送り、元の恒等射の保存を使う。
規約：証明の選択に依存しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCutIntervalMap_id (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) (i : Fin (n + 1)) :
    walkingAdjunctionCutIntervalMap a b h (le_refl i) = OrderHom.id := by
  apply OrderHom.ext
  funext k
  apply walkingAdjunctionCutIntervalInclusion_injective a b h i
  have hs := walkingAdjunctionCutInterval_square_apply a b h (le_refl i) k
  simpa only [homOfLE_refl, CategoryTheory.Functor.map_id, walkingAdjunctionOrderHom_id,
    OrderHom.id_coe, id_eq] using hs

/-- 概要：切れ目の間の射は全合成を保つ。
方針：単射な実包含へ送り、二つの正方形と元の合成保存を使う。
規約：全ての三頂点と射。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCutIntervalMap_comp (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    walkingAdjunctionCutIntervalMap a b h (hij.trans hjk) =
      (walkingAdjunctionCutIntervalMap a b h hjk).comp
        (walkingAdjunctionCutIntervalMap a b h hij) := by
  apply OrderHom.ext
  funext x
  apply walkingAdjunctionCutIntervalInclusion_injective a b h k
  have hc : walkingAdjunctionOrderHom (F.map (homOfLE (hij.trans hjk))) =
      (walkingAdjunctionOrderHom (F.map (homOfLE hjk))).comp
        (walkingAdjunctionOrderHom (F.map (homOfLE hij))) := by
    rw [← homOfLE_comp hij hjk, CategoryTheory.Functor.map_comp, walkingAdjunctionOrderHom_comp]
  rw [walkingAdjunctionCutInterval_square_apply, hc]
  change walkingAdjunctionOrderHom (F.map (homOfLE hjk))
      (walkingAdjunctionOrderHom (F.map (homOfLE hij))
        (walkingAdjunctionCutIntervalInclusion a b h i x)) = _
  exact (congrArg (walkingAdjunctionOrderHom (F.map (homOfLE hjk)))
    (walkingAdjunctionCutInterval_square_apply a b h hij x).symm).trans
      (walkingAdjunctionCutInterval_square_apply a b h hjk
        (walkingAdjunctionCutIntervalMap a b h hij x)).symm

/-- 概要：切れ目の間へ制限した射は、両端の中点の種類が要求する端点を保つ。
方針：実包含の正方形で共有点を評価し、始点のずれを相殺する。
規約：端点条件を引数として追加しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCutIntervalMap_boundary (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    WalkingAdjunctionOrderBoundary M N (walkingAdjunctionCutIntervalMap a b h hij) := by
  constructor
  · intro hM x hx
    subst M
    have he : walkingAdjunctionCutIntervalInclusion a b h i x = a.value i := by
      apply Fin.ext
      change (a.value i).val + x.val = (a.value i).val
      omega
    have hs := walkingAdjunctionCutInterval_square_apply a b h hij x
    rw [he, a.naturality hij] at hs
    have hv := congrArg Fin.val hs
    change (a.value j).val + (walkingAdjunctionCutIntervalMap a b h hij x).val =
      (a.value j).val at hv
    omega
  · intro hN x hx
    subst N
    have hab := walkingAdjunctionCutCoordinate_le a b i (h i)
    have he : walkingAdjunctionCutIntervalInclusion a b h i x = b.value i := by
      apply Fin.ext
      change walkingAdjunctionCutCoordinate a i + x.val = (b.value i).val
      change x.val + 1 = (b.value i).val - walkingAdjunctionCutCoordinate a i + 1 at hx
      change walkingAdjunctionCutCoordinate a i ≤ (b.value i).val at hab
      omega
    have hs := walkingAdjunctionCutInterval_square_apply a b h hij x
    rw [he, b.naturality hij] at hs
    have hv := congrArg Fin.val hs
    change walkingAdjunctionCutCoordinate a j + (walkingAdjunctionCutIntervalMap a b h hij x).val =
      (b.value j).val at hv
    change (walkingAdjunctionCutIntervalMap a b h hij x).val + 1 =
      (b.value j).val - walkingAdjunctionCutCoordinate a j + 1
    omega

end SerrePositivity.InfinityCategories.HA.Monads

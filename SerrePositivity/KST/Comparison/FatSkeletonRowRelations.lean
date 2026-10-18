module

public import SerrePositivity.KST.Comparison.FatSkeletonAttachment

/-!
# fat realization の骨格への行の自然性と面関係

概要：小さい行から指定した骨格への射と、面の関係の骨格への制限を構成する。
方針：全体への包含が単射であることから、既存の行の等式を制限する。
規約：Segal 1974 Proposition 1.6 の骨格の付着。
使われ方：境界の面を低い行へ因子化し、骨格の四角形を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：指定した骨格以下の行から、その骨格への射。
方針：行の最小の骨格への射と骨格の包含を合成する。
規約：m ≤ n の証拠を明示する。
使われ方：境界の面を低い行へ写した後の射。
-/
def fatSkeletonRowOfLE (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) {m n : ℕ} (h : m ≤ n) :
    F.obj (op ⦋m⦌) ⊗ Δ[m] ⟶ (fatSkeleton F n : SSet.{u}) :=
  fatSkeletonRow F m ≫ SSet.Subcomplex.homOfLE (fatSkeleton_monotone F h)

/--
概要：小さい行の骨格への射と全体への包含の合成。
方針：部分対象の包含の合成を計算する。
規約：右辺は元の行の包含。
使われ方：面の関係を包含の単射性で示す。
-/
@[reassoc] theorem fatSkeletonRowOfLE_ι (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    {m n : ℕ} (h : m ≤ n) :
    fatSkeletonRowOfLE F h ≫ (fatSkeleton F n).ι = fatRealizationInclusion F m := rfl

/--
概要：行から骨格への射は二重単体集合の射について自然。
方針：全体への包含を消去して、fat realization の行の自然性を使う。
規約：同じ番号の骨格を比較する。
使われ方：有限骨格の各行の可換四角形。
-/
@[reassoc] theorem fatSkeletonRowOfLE_map
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) {m n : ℕ} (h : m ≤ n) :
    fatSkeletonRowOfLE F h ≫ fatSkeletonMap α n =
      (α.app (op ⦋m⦌) ▷ Δ[m]) ≫ fatSkeletonRowOfLE G h := by
  apply (cancel_mono (fatSkeleton G n).ι).mp
  simp only [Category.assoc, fatSkeletonMap_ι, fatSkeletonRowOfLE_ι_assoc,
    fatSkeletonRowOfLE_ι, fatRealizationInclusion_map]

/--
概要：境界の付着写像は二重単体集合の射について自然。
方針：全体への包含を消去して行の自然性と積の交換を計算する。
規約：境界の番号は n + 1。
使われ方：付着の span の自然変換。
-/
@[reassoc] theorem fatBoundaryAttachment_map
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) (n : ℕ) :
    fatBoundaryAttachment F n ≫ fatSkeletonMap α n =
      (α.app (op ⦋n + 1⦌) ▷ (SSet.boundary (n + 1) : SSet.{u})) ≫
        fatBoundaryAttachment G n := by
  apply (cancel_mono (fatSkeleton G n).ι).mp
  simp only [Category.assoc, fatSkeletonMap_ι, fatBoundaryAttachment_ι_assoc,
    fatBoundaryAttachment_ι, fatRealizationInclusion_map]
  rw [← Category.assoc, whisker_exchange, Category.assoc]

/--
概要：骨格の行の射は単射な面の関係を満たす。
方針：全体への包含を消去し、fat realization の面の関係を使う。
規約：両方の行は指定した骨格以下。
使われ方：境界の面上の射を小さい行に因子化する。
-/
theorem fatSkeletonRowOfLE_face (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (θ : SimplexFace)
    {n : ℕ} (hs : θ.source ≤ n) (ht : θ.target ≤ n) :
    (F.map θ.hom.op ▷ Δ[θ.source]) ≫ fatSkeletonRowOfLE F hs =
      (F.obj (op ⦋θ.target⦌) ◁ SSet.stdSimplex.map θ.hom) ≫ fatSkeletonRowOfLE F ht := by
  apply (cancel_mono (fatSkeleton F n).ι).mp
  simpa only [Category.assoc, fatSkeletonRowOfLE_ι] using fatRealizationInclusion_face F θ

/--
概要：新しい行の境界の面は、小さい行を経由して旧骨格へ写る。
方針：面の包含の等式を積に適用し、fat realization の面の関係を使う。
規約：境界の面を表示する写像 t とその包含の等式を明示する。
使われ方：境界の各面の四角形への帰納仮定の適用。
-/
theorem fatBoundaryAttachment_face (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    {m n : ℕ} (hm : m ≤ n) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (hθ : Function.Injective θ)
    (t : Δ[m] ⟶ (SSet.boundary (n + 1) : SSet.{u}))
    (ht : t ≫ (SSet.boundary (n + 1)).ι = SSet.stdSimplex.map θ) :
    (F.obj (op ⦋n + 1⦌) ◁ t) ≫ fatBoundaryAttachment F n =
      (F.map θ.op ▷ Δ[m]) ≫ fatSkeletonRowOfLE F hm := by
  apply (cancel_mono (fatSkeleton F n).ι).mp
  simp only [Category.assoc, fatBoundaryAttachment_ι, fatSkeletonRowOfLE_ι]
  rw [← Category.assoc, ← whiskerLeft_comp, ht]
  exact (fatRealizationInclusion_face F ⟨m, n + 1, θ, hθ⟩).symm

end SerrePositivity.KST.Comparison

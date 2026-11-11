module
public import SerrePositivity.KST.SConstruction.GappedIso
public import SerrePositivity.KST.SConstruction.CofiberMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-! # 頂点ごとに変わる時刻での自然同値の評価
概要：自然同値の時刻を添字に応じて変えても、始点の図式と関手として同型となる。
方針：時刻と指定時刻の min による prism を作り、各頂点での辺の可逆性を判定する。
規約：任意の自然変換を同値とは扱わない。使われ方：object S の自然同値によるホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：二つの区間の時刻の最小値を取る順序写像。
方針：min の単調性。
規約：ULift で宇宙を合わせる。使われ方：可変時刻の prism。 -/
def intervalMinOrder : ULift.{u} (Fin 2 × Fin 2) →o ULift.{u} (Fin 2) where
  toFun p := ULift.up (min p.down.1 p.down.2)
  monotone' _ _ h := min_le_min h.1 h.2

/-- 概要：二つの標準区間の時刻の最小値を取る単体的射。
方針：順序写像の nerve を標準単体の表示へ移す。
規約：全次数で自然。使われ方：始点から可変時刻へのホモトピー。 -/
def intervalMin : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[1] :=
  (prodStdSimplex.isoNerve 1 1).hom ≫ nerveMap intervalMinOrder.toFunctor ≫
    (stdSimplex.isoNerve 1).inv

/-- 概要：min の第二座標が零の定値単体なら結果も零の定値単体。
方針：鎖の全頂点で min(t,0)=0 を使う。
規約：任意の単体次数。使われ方：可変時刻の辺の始点での可逆性。 -/
lemma intervalMin_app_zero {n : ℕ} (s : (Δ[1] : SSet.{u}) _⦋n⦌) :
    intervalMin.app (Opposite.op ⦋n⦌)
        (s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n := by
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext r
  change min (stdSimplex.asOrderHom s r) 0 = 0
  exact min_eq_right (Fin.zero_le _)

/-- 概要：min の第二座標が一の定値単体なら結果は第一座標。
方針：鎖の全頂点で min(t,1)=t を使う。
規約：任意の単体次数。使われ方：可変時刻の辺の終点での可逆性。 -/
lemma intervalMin_app_one {n : ℕ} (s : (Δ[1] : SSet.{u}) _⦋n⦌) :
    intervalMin.app (Opposite.op ⦋n⦌)
      (s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n) = s := by
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext r
  change min (stdSimplex.asOrderHom s r) 1 = stdSimplex.asOrderHom s r
  exact min_eq_left (Fin.le_last _)

/-- 概要：添字を保ち、時刻を指定された時刻との min に置き換える。
方針：二つの射影と指定時刻を組み合わせる。
規約：ホモトピーの時刻は第二因子。使われ方：自然同値の可変時刻での評価。 -/
def variableTimeShape {A : SSet.{u}} (τ : A ⟶ (Δ[1] : SSet.{u})) : A ⊗ Δ[1] ⟶ A ⊗ Δ[1] :=
  lift (fst A Δ[1]) (lift (snd A Δ[1]) (fst A Δ[1] ≫ τ) ≫ intervalMin)

/-- 概要：可変時刻の prism は時刻零で元の始点。
方針：min(0,t)=0 を各単体で計算する。
規約：厳密等号。使われ方：ホモトピーの始点。 -/
lemma variableTimeShape_zero {A : SSet.{u}} (τ : A ⟶ (Δ[1] : SSet.{u})) :
    SSet.ι₀ ≫ variableTimeShape τ = (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, variableTimeShape, lift_fst]
  · simp only [Category.assoc, variableTimeShape, lift_snd]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext r
    change min 0 (stdSimplex.asOrderHom (τ.app d a) r) = 0
    exact min_eq_left (Fin.zero_le _)

/-- 概要：可変時刻の prism は時刻一で指定時刻のグラフ。
方針：min(1,t)=t を各単体で計算する。
規約：厳密等号。使われ方：ホモトピーの終点。 -/
lemma variableTimeShape_one {A : SSet.{u}} (τ : A ⟶ (Δ[1] : SSet.{u})) :
    SSet.ι₁ ≫ variableTimeShape τ = lift (𝟙 A) τ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, variableTimeShape, lift_fst, SSet.ι₁_fst]
  · simp only [Category.assoc, variableTimeShape, lift_snd]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext r
    change min 1 (stdSimplex.asOrderHom (τ.app d a) r) = stdSimplex.asOrderHom (τ.app d a) r
    exact min_eq_right (Fin.le_last _)

/-- 概要：自然変換を図式上で指定された可変時刻に評価した射。
方針：図式と時刻のグラフを prism へ送る。
規約：可逆性はまだ要求しない。使われ方：object S の候補単体。 -/
def variableTimeImage {A C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) : A ⟶ D := lift F τ ≫ H.h

/-- 概要：可変時刻の図式は添字の制限と厳密に両立する。
方針：図式と時刻の両方を同じ射で制限する。
規約：任意の添字の射。使われ方：object S の単体ホモトピーの自然性。 -/
lemma variableTimeImage_pre {A B C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) (i : B ⟶ A) :
    i ≫ variableTimeImage H F τ = variableTimeImage H (i ≫ F) (i ≫ τ) := by
  dsimp only [variableTimeImage]
  rw [← Category.assoc]
  congr 1

/-- 概要：時刻零で一定な可変時刻の図式は始点の関手の像。
方針：定値時刻のグラフをホモトピーの始点へ分解する。
規約：射の厳密な等号。使われ方：object S のホモトピーの始点。 -/
lemma variableTimeImage_zero {A C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) :
    variableTimeImage H F (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = F ≫ f := by
  have he : lift F (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = F ≫ SSet.ι₀ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [variableTimeImage, he, Category.assoc, H.h₀]

/-- 概要：時刻一で一定な可変時刻の図式は終点の関手の像。
方針：定値時刻のグラフをホモトピーの終点へ分解する。
規約：射の厳密な等号。使われ方：object S のホモトピーの終点。 -/
lemma variableTimeImage_one {A C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) :
    variableTimeImage H F (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = F ≫ g := by
  have he : lift F (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = F ≫ SSet.ι₁ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [variableTimeImage, he, Category.assoc, H.h₁]

/-- 概要：自然変換の始点と可変時刻での評価を結ぶ実際の単体ホモトピー。
方針：時刻を min で動かす prism を自然変換へ後合成する。
規約：可逆性は結論に含めない。使われ方：点ごとの可逆性の判定。 -/
def variableTimeHomotopy {A C D : SSet.{u}} {f g : C ⟶ D} (H : SSet.Homotopy f g)
    (F : A ⟶ C) (τ : A ⟶ (Δ[1] : SSet.{u})) :
    SSet.Homotopy (F ≫ f) (variableTimeImage H F τ) where
  h := variableTimeShape τ ≫ (F ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by
    change SSet.ι₀ ≫ variableTimeShape τ ≫ (F ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ H.h = F ≫ f
    rw [← Category.assoc, variableTimeShape_zero, tensorHom_id, ← Category.assoc,
      SSet.ι₀_comp, Category.assoc, H.h₀]
  h₁ := by
    rw [← Category.assoc, variableTimeShape_one]
    change (lift (𝟙 A) τ ≫ (F ⊗ₘ 𝟙 (Δ[1] : SSet.{u}))) ≫ H.h = _
    have he : lift (𝟙 A) τ ≫ (F ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) = lift F τ := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [he]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.KST.SConstruction

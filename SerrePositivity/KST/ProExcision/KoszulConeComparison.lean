module

public import SerrePositivity.KST.ProExcision.PowerQuotient
public import SerrePositivity.KST.ProExcision.ConeFiniteness
public import SerrePositivity.KST.ProExcision.PowerKernelArtinRees

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 列長帰納法による Koszul の pro 比較

概要：ホモロジーの反復冪商を反復 Koszul cone のホモロジーへ比較する。
方針：短い列の比較を冪商へ降ろし、独立な末尾変数の一変数比較の対角と合成する。
規約：原典のスペクトル系列証明と異なり、cone 長完全列と対角の共終性を使う。
使われ方：KST Lemma 4.10。通常の生成イデアルによる一度の商との同定は別補題。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 概要：動く係数のホモロジーの冪商から、対角冪 cone のホモロジーへの比較。
方針：二重塔の比較を定義通り対角へ制限する。
規約：係数と冪指数は対角上で同時に動く。
使われ方：KST Lemma 4.10 の列長帰納法の最後の比較射。 -/
def diagonalPowerConeComparison (a : R)
    (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ) :
    LevelHom ((X.map (homologyFunctor _ _ i)).powerQuotient a)
      ((powerScalarConeBiTower a X).diagonal.map (homologyFunctor _ _ i)) :=
  (powerScalarConeBiComparison a X i).diagonal

/-- 概要：反復 cone を対角の冪指数で作った Koszul の塔。
方針：列を延ばすごとに末尾変数の冪 cone の二重塔の対角を取る。
規約：各段の複体は既存の koszulComplexOn。
使われ方：KST Lemma 4.9・4.10 の列長帰納法。 -/
def koszulConeTower : ∀ {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ), Tower (CochainComplex (ModuleCat.{u} R) ℤ)
  | 0, _, K => Tower.constant K
  | e + 1, z, K =>
      (powerScalarConeBiTower (z (Fin.last e)) (koszulConeTower (Fin.init z) K)).diagonal

/-- 概要：反復 cone の塔の各段は既存 Koszul 複体の冪係数版。
方針：列長帰納法で定義を比較する。
規約：末尾変数を最後に cone とする。使われ方：KST Lemma 4.10 の既存複体への接続。 -/
theorem koszulConeTower_obj : ∀ {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ),
    (koszulConeTower z K).obj n = koszulComplexOn (fun j ↦ z j ^ n) K
  | 0, _, _, _ => rfl
  | e + 1, z, K, n => by
      change (scalarConeFunctor (z (Fin.last e) ^ n)).obj
        ((koszulConeTower (Fin.init z) K).obj n) = _
      rw [koszulConeTower_obj]
      rfl

/-- 概要：各変数の冪による通常商を順に取った加群の塔。
方針：空列は定数塔とし、末尾変数でさらに冪商を取る。
規約：複体や導来商を使用しない。
使われ方：KST Lemma 4.10 の比較射の通常商側。 -/
def iteratedPowerQuotientTower : ∀ {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R), Tower (ModuleCat.{u} R)
  | 0, _, M => Tower.constant M
  | e + 1, z, M => (iteratedPowerQuotientTower (Fin.init z) M).powerQuotient (z (Fin.last e))

/-- 概要：反復通常商から反復 Koszul cone のホモロジーへの標準比較。
方針：短い列の比較を末尾変数の冪商へ降ろし、cone の一変数比較と合成する。
規約：全ての段と遷移を持つレベル射。
使われ方：KST Lemma 4.10 の長完全列による比較。 -/
def koszulConeComparison : ∀ {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
    LevelHom (iteratedPowerQuotientTower z (K.homology i))
      ((koszulConeTower z K).map (homologyFunctor _ _ i))
  | 0, _, K, i =>
      { app _ := 𝟙 (K.homology i)
        naturality _ := by
          change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ homologyMap (𝟙 K) i
          rw [homologyMap_id] }
  | e + 1, z, K, i =>
      LevelHom.comp ((koszulConeComparison (Fin.init z) K i).powerQuotient (z (Fin.last e)))
        (diagonalPowerConeComparison (z (Fin.last e)) (koszulConeTower (Fin.init z) K) i)

/-- 概要：反復通常冪商と Koszul cone ホモロジーの比較は pro 同型。
方針：列長帰納法、動く冪商による pro 同型保存、二重 cone 比較の対角を使う。
規約：Noether 環上で各係数ホモロジーが有限生成。項の有限性・複体の有界性は要求しない。
使われ方：KST Lemma 4.10 の長完全列経路の中心命題。 -/
theorem koszulConeComparison_isProIso [IsNoetherianRing R] :
    ∀ {e : ℕ} (z : Fin e → R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, Module.Finite R (K.homology i)) (i : ℤ),
    IsProIso (koszulConeComparison z K i)
  | 0, _, K, iK, i => by
      intro n
      refine ⟨n, le_refl n, 𝟙 _, ?_, ?_⟩
      · exact Category.id_comp _
      · change 𝟙 _ ≫ 𝟙 _ = homologyMap (𝟙 K) i
        rw [homologyMap_id, Category.id_comp]
  | e + 1, z, K, hK, i => by
      apply IsProIso.comp
        ((koszulConeComparison_isProIso (Fin.init z) K hK i).powerQuotient (z (Fin.last e)))
      apply powerScalarConeBiComparison_diagonal_isProIso_artinRees
      intro n
      rw [koszulConeTower_obj]
      exact koszulComplexOn_homology_finite (fun j ↦ (Fin.init z) j ^ n) K hK (i + 1)

end SerrePositivity.KST.ProExcision

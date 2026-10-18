module

public import SerrePositivity.KST.Spectra.PathContractibility
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-!
概要：点つき対象の基点を固定するホモトピーの相対表示。
方針：基点生成部分複体の包含を定数射と同定する。
規約：ホモトピーは全区間で基点を固定する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1。置換と整数次数の不変性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき射間の基点固定ホモトピーを基点部分複体に相対なホモトピーへ移す。
方針：基点の定数射の表示と全時刻での基点固定式を使う。
規約：源・標的の Kan 性はこの変換に不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1。π_* の不変性。 -/
def pointedRelativeHomotopy {X Y : PointedSimplicialSet.{u}} (f g : X ⟶ Y)
    (H : SSet.Homotopy f.right g.right)
    (hbase : X.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom) :
    (RelativeMorphism.ofSimplex₀ f.right X.basepoint Y.basepoint
      (OmegaSpectrum.pointedMap_basepoint f)).Homotopy
      (RelativeMorphism.ofSimplex₀ g.right X.basepoint Y.basepoint
        (OmegaSpectrum.pointedMap_basepoint g)) where
  h := H.h
  h₀ := H.h₀
  h₁ := H.h₁
  rel := by
    rw [Subcomplex.ofSimplex_ι, ← pointedConstant_eq_const X,
      comp_whiskerRight_assoc, hbase, comp_toUnit_assoc]
    rw [SSet.const_comp, SSet.comp_const]
    exact pointedConstant_eq_const Y _

/-- 概要：点つき Kan 複体の射による全自然数次数の誘導写像。
方針：点つき射の基点保存を通常の誘導写像へ渡す。
規約：零次数では集合の写像。
使われ方：Goerss–Jardine I §7。置換のホモトピー逆の計算。 -/
def pointedHomotopyMap {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (n : ℕ) (f : X ⟶ Y) :
    KanHomotopy X.right n X.basepoint → KanHomotopy Y.right n Y.basepoint :=
  KanHomotopy.map n f.right (OmegaSpectrum.pointedMap_basepoint f)

/-- 概要：点つき誘導写像は恒等射を保つ。
方針：通常のホモトピー類の恒等法則を使う。
規約：全自然数次数。
使われ方：Goerss–Jardine I §7。置換比較の逆の計算。 -/
@[simp]
theorem pointedHomotopyMap_id (X : PointedSimplicialSet.{u}) [KanComplex X.right]
    (n : ℕ) (a : KanHomotopy X.right n X.basepoint) :
    pointedHomotopyMap n (𝟙 X) a = a := KanHomotopy.map_id n a

/-- 概要：点つき誘導写像は合成を保つ。
方針：基点保存の証明の一意性と通常の合成法則を使う。
規約：全自然数次数。
使われ方：Goerss–Jardine I §7。置換のホモトピー逆の照合。 -/
theorem pointedHomotopyMap_comp {X Y Z : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] [KanComplex Z.right]
    (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) (a : KanHomotopy X.right n X.basepoint) :
    pointedHomotopyMap n (f ≫ g) a = pointedHomotopyMap n g (pointedHomotopyMap n f a) :=
  KanHomotopy.map_comp n f.right _ g.right _ _ a

/-- 概要：各段で基点固定ホモトピックなスペクトルの射は同じ整数次数の準同型を誘導する。
方針：標準段での全自然数次数のホモトピー不変性を使う。
規約：ホモトピーの族は実際の相対ホモトピーとして与える。
使われ方：BF 1978 §2、HA §1.4.2。置換のホモトピー比較。 -/
theorem OmegaSpectrum.homotopyMap_eq_of_levelHomotopy {X Y : OmegaSpectrum.{u}}
    (f g : X ⟶ Y)
    (H : ∀ k, (RelativeMorphism.ofSimplex₀ (f.app k).right
      (X.level k).space.basepoint (Y.level k).space.basepoint
        (pointedMap_basepoint _)).Homotopy
      (RelativeMorphism.ofSimplex₀ (g.app k).right
        (X.level k).space.basepoint (Y.level k).space.basepoint
          (pointedMap_basepoint _))) (j : ℤ) : homotopyMap f j = homotopyMap g j := by
  apply MonoidHom.ext
  intro a
  rw [homotopyMap_apply, homotopyMap_apply]
  exact KanHomotopy.map_eq_of_basedHomotopy _ _ _ (H _) a

end

end SerrePositivity.KST.Spectra

module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# span の基底の二射の単射への置換

概要：span の二つの水平射を単射に置き換え、元の span へ成分ごとの局所化同型を与える。
方針：既存の mono–全単射的右持ち上げ性の分解を二つの脚に適用する。
規約：Segal 1974 Lemma 1.7 の単射な基底の場合への還元。中央の対象は元のものを使う。
使われ方：縦の Kan fibration を基底変換して単射な基底の貼り合わせを適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：二つの脚を単射に置き換えた span。
方針：各脚の mono 分解の前半を使う。
規約：中央の対象は元の span の零頂点。
使われ方：単射な基底の貼り合わせへの入力。
-/
def spanMonoBase (G : WalkingSpan ⥤ SSet.{u}) : WalkingSpan ⥤ SSet.{u} :=
  span (MonoLocalizedFactorization.left (G.map WalkingSpan.Hom.fst))
    (MonoLocalizedFactorization.left (G.map WalkingSpan.Hom.snd))

/--
概要：単射な基底の span から元の span への標準射。
方針：中央では恒等射、両端では mono 分解の後半を使う。
規約：可換性は元の二つの射の因子化の式。
使われ方：元の縦射を基底変換する比較。
-/
def spanMonoBaseProjection (G : WalkingSpan ⥤ SSet.{u}) : spanMonoBase G ⟶ G :=
  spanHomMk (𝟙 _) (MonoLocalizedFactorization.right (G.map WalkingSpan.Hom.fst))
    (MonoLocalizedFactorization.right (G.map WalkingSpan.Hom.snd))
    (by
      change MonoLocalizedFactorization.left (G.map WalkingSpan.Hom.fst) ≫
        MonoLocalizedFactorization.right (G.map WalkingSpan.Hom.fst) =
          𝟙 _ ≫ G.map WalkingSpan.Hom.fst
      rw [Category.id_comp]
      exact MonoLocalizedFactorization.fac _)
    (by
      change MonoLocalizedFactorization.left (G.map WalkingSpan.Hom.snd) ≫
        MonoLocalizedFactorization.right (G.map WalkingSpan.Hom.snd) =
          𝟙 _ ≫ G.map WalkingSpan.Hom.snd
      rw [Category.id_comp]
      exact MonoLocalizedFactorization.fac _)

/--
概要：置換した span の左脚は単射である。
方針：mono 分解の前半の性質を使う。
規約：元の射の単射性は不要。
使われ方：左ファイバーの端点への包含の単射性。
-/
instance spanMonoBase_fst_mono (G : WalkingSpan ⥤ SSet.{u}) :
    Mono ((spanMonoBase G).map WalkingSpan.Hom.fst) :=
  inferInstanceAs (Mono (MonoLocalizedFactorization.left (G.map WalkingSpan.Hom.fst)))

/--
概要：置換した span の右脚は単射である。
方針：mono 分解の前半の性質を使う。
規約：元の射の単射性は不要。
使われ方：右ファイバーの端点への包含の単射性。
-/
instance spanMonoBase_snd_mono (G : WalkingSpan ⥤ SSet.{u}) :
    Mono ((spanMonoBase G).map WalkingSpan.Hom.snd) :=
  inferInstanceAs (Mono (MonoLocalizedFactorization.left (G.map WalkingSpan.Hom.snd)))

/--
概要：中央の基底の Kan 性は、単射な基底への置換でも使える。
方針：中央の対象の定義をそのまま使う。
規約：端点の対象の Kan 性は要求しない。
使われ方：単射な基底の貼り合わせの中央の仮定。
-/
instance spanMonoBase_zero_kanComplex (G : WalkingSpan ⥤ SSet.{u})
    [SSet.KanComplex (G.obj .zero)] : SSet.KanComplex ((spanMonoBase G).obj .zero) :=
  inferInstanceAs (SSet.KanComplex (G.obj .zero))

/--
概要：単射な基底への置換から元の span への比較は、全ての成分で局所化同型である。
方針：中央の恒等射と、両端の全単射的右持ち上げ性の可逆性を使う。
規約：モデル構造の追加仮定は使わない。
使われ方：基底変換による元の図式との比較。
-/
theorem spanMonoBaseProjection_localized_isIso (G : WalkingSpan ⥤ SSet.{u}) (d : WalkingSpan) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((spanMonoBaseProjection G).app d)) := by
  rcases d with (_ | _ | _)
  · change IsIso (AnodyneHomotopy.anodyneQ.map (𝟙 (G.obj .zero))); infer_instance
  · exact MonoLocalizedFactorization.right_localized_isIso (G.map WalkingSpan.Hom.fst)
  · exact MonoLocalizedFactorization.right_localized_isIso (G.map WalkingSpan.Hom.snd)

end SerrePositivity.KST.Comparison

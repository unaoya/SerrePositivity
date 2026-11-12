module

public import SerrePositivity.KST.Comparison.ReplacementComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 別の Kan 分解でホモトピー引き戻しを計算する

概要：右射の任意の anodyne–Kan 分解で標準比較射の可逆性を判定する。
方針：二分解の間の持ち上げを引き戻し、分解比較の局所化可逆性を使う。
規約：Segal 1974 Proposition 1.6・Lemma 1.7 のホモトピー引き戻し模型の独立性。
使われ方：bar の行の積射影を、モノイドの Kan 置換を使う分解で扱う。
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
概要：右射の指定した分解を用いて四角形の比較射を作る。
方針：右成分に分解の前半を合成し、後半の引き戻しへ持ち上げる。
規約：Segal 1974 Proposition 1.6。ここでは分解の可換性だけを要求する。
使われ方：標準分解と別の分解の比較。
-/
def alternativePullbackComparison {P X Y Z T : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g)
    (i : Y ⟶ T) (p : T ⟶ Z) (h : i ≫ p = g) : P ⟶ pullback f p :=
  pullback.lift a (b ≫ i) (by rw [Category.assoc, h]; exact sq.w)

/--
概要：指定分解を用いた比較射の第一射影は元の第一成分である。
方針：引き戻しへの持ち上げの計算則を使う。
規約：Segal 1974 Proposition 1.6。
使われ方：二分解を比較する三角形。
-/
@[reassoc] theorem alternativePullbackComparison_fst {P X Y Z T : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g)
    (i : Y ⟶ T) (p : T ⟶ Z) (h : i ≫ p = g) :
    alternativePullbackComparison sq i p h ≫ pullback.fst f p = a := pullback.lift_fst ..

/--
概要：指定分解を用いた比較射の第二射影は元の第二成分の置換である。
方針：引き戻しへの持ち上げの計算則を使う。
規約：Segal 1974 Proposition 1.6。
使われ方：二分解の比較射の自然性。
-/
@[reassoc] theorem alternativePullbackComparison_snd {P X Y Z T : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g)
    (i : Y ⟶ T) (p : T ⟶ Z) (h : i ≫ p = g) :
    alternativePullbackComparison sq i p h ≫ pullback.snd f p = b ≫ i := pullback.lift_snd ..

/--
概要：ホモトピー引き戻し性は右射の別の anodyne–Kan 分解でも判定できる。
方針：別分解から標準分解への基底上の持ち上げを引き戻し、局所化同型を打ち消す。
規約：Segal 1974 Proposition 1.6・Lemma 1.7。分解の同値性を追加仮定にしない。
使われ方：積射影のホモトピー引き戻し性。
-/
@[kerodon 010L, kerodon 010N]
theorem isHomotopyPullback_iff_alternative {P X Y Z T : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g)
    (i : Y ⟶ T) (hi : SSet.anodyneExtensions i) (p : T ⟶ Z)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (h : i ≫ p = g) :
    IsHomotopyPullback sq ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (alternativePullbackComparison sq i p h)) := by
  let d := AnodyneKanReplacement.factorization.factorizationData g
  have : HasLiftingProperty i d.p := hi _ d.hp
  let s : CommSq d.i i d.p p := ⟨d.fac.trans h.symm⟩
  let k := s.lift
  have hik : i ≫ k = d.i := s.fac_left
  have hkp : k ≫ d.p = p := s.fac_right
  let u := pullbackMapBase p d.p f k hkp
  have hu : IsIso (AnodyneHomotopy.anodyneQ.map u) :=
    replacementComparison_pullback_isIso i hi d.i d.hi p hp d.p d.hp
      (h.trans d.fac.symm) k hik hkp f
  let t := alternativePullbackComparison sq i p h
  let c : P ⟶ pullback f d.p := homotopyPullbackComparison sq
  have hcf : c ≫ pullback.fst f d.p = a := homotopyPullbackComparison_fst sq
  have hcs : c ≫ pullback.snd f d.p = b ≫ d.i := homotopyPullbackComparison_snd sq
  have hct : t ≫ u = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackMapBase_fst, alternativePullbackComparison_fst, hcf]
    · rw [Category.assoc, pullbackMapBase_snd, hcs]
      rw [← Category.assoc t (pullback.snd f p) k, alternativePullbackComparison_snd,
        Category.assoc, hik]
  change IsIso (AnodyneHomotopy.anodyneQ.map c) ↔ IsIso (AnodyneHomotopy.anodyneQ.map t)
  rw [← hct, AnodyneHomotopy.anodyneQ.map_comp]
  exact isIso_comp_right_iff _ _

end SerrePositivity.KST.Comparison

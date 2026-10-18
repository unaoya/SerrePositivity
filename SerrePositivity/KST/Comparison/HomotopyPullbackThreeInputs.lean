module

public import SerrePositivity.KST.Comparison.FibrantCospanInvariance
public import SerrePositivity.KST.Comparison.HomotopyPullbackInvariance

/-!
# ホモトピー引き戻しの基底を含む三入力の不変性

概要：基底と左右の入力の局所化同型は、実際のホモトピー引き戻し模型の局所化同型を誘導する。
方針：右入力の関手的な分解の比較を作り、Kan fibration の cospan の不変性を使う。
規約：Segal 1974 Proposition 1.6 の貼り合わせに使う模型の不変性。
使われ方：四角形の各頂点を同時に置換する。
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
概要：基底を含む三成分が局所化同型なら、ホモトピー引き戻しの標準比較も局所化同型である。
方針：右射の anodyne–Kan 分解の中間対象の比較を二対三で可逆とし、cospan の比較へ適用する。
規約：基底や左右の入力の Kan 性を要求しない。
使われ方：模型の選択の不変性と、四つの頂点の置換。
-/
theorem homotopyPullbackMap_localized_isIso {X Y B X' Y' B' : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (a : X ⟶ X') (b : Y ⟶ Y') (c : B ⟶ B')
    (hf : f ≫ c = a ≫ f') (hg : g ≫ c = b ≫ g')
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hb : IsIso (AnodyneHomotopy.anodyneQ.map b))
    (hc : IsIso (AnodyneHomotopy.anodyneQ.map c)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackMap a b c hf hg)) := by
  let d₀ := AnodyneKanReplacement.factorization.factorizationData g
  let d₁ := AnodyneKanReplacement.factorization.factorizationData g'
  let φ : Arrow.mk g ⟶ Arrow.mk g' := Arrow.homMk b c hg.symm
  let z : d₀.Z ⟶ d₁.Z := AnodyneKanReplacement.factorization.Z.map φ
  have hz : z ≫ d₁.p = d₀.p ≫ c := AnodyneKanReplacement.factorization.p.naturality φ
  have hi : d₀.i ≫ z = b ≫ d₁.i :=
    (AnodyneKanReplacement.factorization.i.naturality φ).symm
  have hi₀ : IsIso (AnodyneHomotopy.anodyneQ.map d₀.i) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions d₀.i d₀.hi
  have hi₁ : IsIso (AnodyneHomotopy.anodyneQ.map d₁.i) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions d₁.i d₁.hi
  have hzi : IsIso (AnodyneHomotopy.anodyneQ.map z) := by
    have hcomp : IsIso (AnodyneHomotopy.anodyneQ.map d₀.i ≫
        AnodyneHomotopy.anodyneQ.map z) := by
      rw [← Functor.map_comp, hi, Functor.map_comp]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hcomp
  exact fibrantCospanMap_localized_isIso f d₀.p d₀.hp f' d₁.p d₁.hp
    a z c hf hz.symm ha hzi hc (homotopyPullbackMap a b c hf hg)
    (homotopyPullbackMap_fst a b c hf hg) (homotopyPullbackMap_snd a b c hf hg)

/--
概要：四角形の比較はホモトピー引き戻しへの標準比較射と可換である。
方針：二つの射影を計算し、右射の分解の単位の自然性を使う。
規約：上側の二つの可換条件は各頂点の写像と元の脚の整合。
使われ方：四つの頂点の局所化同型によるホモトピー引き戻し性の不変性。
-/
theorem homotopyPullbackComparison_naturality {P X Y B P' X' Y' B' : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    {a' : P' ⟶ X'} {b' : P' ⟶ Y'} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (sq : CommSq a b f g) (sq' : CommSq a' b' f' g')
    (uP : P ⟶ P') (uX : X ⟶ X') (uY : Y ⟶ Y') (uB : B ⟶ B')
    (hA : a ≫ uX = uP ≫ a') (hB : b ≫ uY = uP ≫ b')
    (hf : f ≫ uB = uX ≫ f') (hg : g ≫ uB = uY ≫ g') :
    homotopyPullbackComparison sq ≫ homotopyPullbackMap uX uY uB hf hg =
      uP ≫ homotopyPullbackComparison sq' := by
  let φ : Arrow.mk g ⟶ Arrow.mk g' := Arrow.homMk uY uB hg.symm
  let z := AnodyneKanReplacement.factorization.Z.map φ
  have hi : AnodyneKanReplacement.factorization.i.app (Arrow.mk g) ≫ z =
      uY ≫ AnodyneKanReplacement.factorization.i.app (Arrow.mk g') :=
    (AnodyneKanReplacement.factorization.i.naturality φ).symm
  apply pullback.hom_ext
  · rw [Category.assoc, homotopyPullbackMap_fst, ← Category.assoc,
      homotopyPullbackComparison_fst, Category.assoc, homotopyPullbackComparison_fst]
    exact hA
  · have hms : homotopyPullbackMap uX uY uB hf hg ≫
        pullback.snd f' (AnodyneKanReplacement.factorization.p.app (Arrow.mk g')) =
      pullback.snd f (AnodyneKanReplacement.factorization.p.app (Arrow.mk g)) ≫ z :=
      homotopyPullbackMap_snd uX uY uB hf hg
    rw [Category.assoc, hms, ← Category.assoc, homotopyPullbackComparison_snd,
      Category.assoc, hi, ← Category.assoc, hB]
    simp only [Category.assoc, homotopyPullbackComparison_snd]

/--
概要：四つの頂点の局所化同型による四角形の比較は、ホモトピー引き戻し性を保存・反映する。
方針：標準比較射の自然性と、三入力の比較の可逆性を二対三で使う。
規約：基底の Kan 性や模型の選択の同一性を要求しない。
使われ方：Ex∞ による四角形全体の置換。
-/
theorem isHomotopyPullback_iff_of_localized_isIso {P X Y B P' X' Y' B' : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    {a' : P' ⟶ X'} {b' : P' ⟶ Y'} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (sq : CommSq a b f g) (sq' : CommSq a' b' f' g')
    (uP : P ⟶ P') (uX : X ⟶ X') (uY : Y ⟶ Y') (uB : B ⟶ B')
    (hA : a ≫ uX = uP ≫ a') (hB : b ≫ uY = uP ≫ b')
    (hf : f ≫ uB = uX ≫ f') (hg : g ≫ uB = uY ≫ g')
    (hP : IsIso (AnodyneHomotopy.anodyneQ.map uP))
    (hX : IsIso (AnodyneHomotopy.anodyneQ.map uX))
    (hY : IsIso (AnodyneHomotopy.anodyneQ.map uY))
    (hZ : IsIso (AnodyneHomotopy.anodyneQ.map uB)) :
    IsHomotopyPullback sq ↔ IsHomotopyPullback sq' := by
  have hm := homotopyPullbackMap_localized_isIso uX uY uB hf hg hX hY hZ
  have h := congrArg AnodyneHomotopy.anodyneQ.map
    (homotopyPullbackComparison_naturality sq sq' uP uX uY uB hA hB hf hg)
  rw [Functor.map_comp, Functor.map_comp] at h
  change IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison sq)) ↔
    IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison sq'))
  calc
    _ ↔ IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison sq) ≫
        AnodyneHomotopy.anodyneQ.map (homotopyPullbackMap uX uY uB hf hg)) :=
      (isIso_comp_right_iff _ _).symm
    _ ↔ IsIso (AnodyneHomotopy.anodyneQ.map uP ≫
        AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison sq')) := by rw [h]
    _ ↔ _ := isIso_comp_left_iff _ _

end SerrePositivity.KST.Comparison

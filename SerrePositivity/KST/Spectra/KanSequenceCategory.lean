module

public import SerrePositivity.KST.Spectra.KanSequence

/-!
概要：構造射の単射性をまだ要求しない Kan 列の厳密な圏。
方針：既存の段ごとの射と合成を圏の構造へまとめる。
規約：Ω 条件は対象に含めず、必要な図式で個別に仮定する。
使われ方：BF 1978 §2、HA §1.4.2。源の置換と可換な telescope の図式の構成。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.KanSequence

/-- 概要：Kan 列の厳密な射は各段の射で決まる。
方針：構造可換式は命題であるため段の関数の外延性だけを使う。
規約：各段の厳密な等式を仮定する。
使われ方：BF 1978 §2。列の圏の法則と図式の自然性の判定。 -/
theorem Hom.ext_app {X Y : KanSequence.{u}} (f g : Hom X Y)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      subst g
      rfl

/-- 概要：Kan 列と厳密な構造可換射は通常の圏をなす。
方針：各段の恒等射と既存の合成を使い、法則は段ごとに示す。
規約：ホモトピー類の圏ではない。
使われ方：BF 1978 §2、HA §1.4.2。単射置換前の telescope の関手的な図式。 -/
instance : Category.{u} KanSequence.{u} where
  Hom := Hom
  id X := { app n := 𝟙 _, comm n := by simp }
  comp f g := f.comp g
  id_comp f := by apply Hom.ext_app; intro n; exact Category.id_comp (f.app n)
  comp_id f := by apply Hom.ext_app; intro n; exact Category.comp_id (f.app n)
  assoc f g h := by
    apply Hom.ext_app
    intro n
    exact Category.assoc (f.app n) (g.app n) (h.app n)

/-- 概要：Kan 列の恒等射は各段で恒等射。
方針：圏構造の定義を開く。
規約：単射構造射を要求しない列の圏。
使われ方：BF 1978 §2。評価関手の恒等射の法則。 -/
@[simp]
theorem id_app (X : KanSequence.{u}) (n : ℕ) : (𝟙 X : X ⟶ X).app n = 𝟙 _ := rfl

/-- 概要：Kan 列の射の合成は段ごとの合成。
方針：既存の厳密な合成の定義を使う。
規約：通常の圏の合成記号を使う。
使われ方：BF 1978 §2。評価関手と自然変換の構成。 -/
@[simp]
theorem comp_app {X Y Z : KanSequence.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- 概要：Kan 列を指定した段の点つき単体集合で評価する関手。
方針：射をその段の成分へ送る。
規約：通常の厳密な列の圏の関手。
使われ方：Goerss–Jardine I §7。図式の段ごとの filtered 余極限。 -/
def levelEvaluation (k : ℕ) : KanSequence.{u} ⥤ PointedSimplicialSet.{u} where
  obj X := (X.level k).space
  map f := f.app k
  map_id _ := rfl
  map_comp _ _ := rfl

end SerrePositivity.KST.Spectra.KanSequence

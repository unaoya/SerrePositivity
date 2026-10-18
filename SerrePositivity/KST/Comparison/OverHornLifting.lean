module

public import SerrePositivity.KST.Comparison.SliceAdjunction
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# スライス圏における horn の持ち上げ

概要：基底を指定した horn の持ち上げと、忘却後の Kan fibration を対応させる。
方針：対角射の基底への合成は、右の成分との合成から決まる。
規約：Segal 1974 Proposition 1.6 の基底変換の補助。全 horn を用いる。
使われ方：随伴の右側で得た射の Kan 性を検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open scoped Simplicial

/--
概要：指定された基底への標準単体の写像の上にある horn 包含。
方針：horn の構造射は包含と基底への写像の合成とする。
規約：次元は n+1 で正次元に限る。
使われ方：スライス内で Kan 条件をテストする。
-/
def hornOverMap {B : SSet.{u}} {n : ℕ} (k : Fin (n + 2)) (b : (Δ[n + 1] : SSet.{u}) ⟶ B) :
    Over.mk ((Λ[n + 1, k]).ι ≫ b) ⟶ Over.mk b := Over.homMk (Λ[n + 1, k]).ι

/--
概要：忘却後の持ち上げ性はスライス内の持ち上げ性を与える。
方針：対角射が基底を保つことを、右辺との合成の条件から示す。
規約：基底に関する追加の持ち上げ性は仮定しない。
使われ方：anodyne 射の左持ち上げ性をスライス内で使う。
-/
theorem over_lifting_of_underlying {B : SSet.{u}} {X Y E T : Over B}
    (i : X ⟶ Y) (p : E ⟶ T) (hi : HasLiftingProperty i.left p.left) : HasLiftingProperty i p := by
  let := hi
  constructor
  intro a b sq
  let sq' : CommSq a.left i.left p.left b.left := ⟨congrArg (fun f => f.left) sq.w⟩
  let l : Y ⟶ E := Over.homMk sq'.lift (by
    calc
      sq'.lift ≫ E.hom = sq'.lift ≫ (p.left ≫ T.hom) := by rw [Over.w p]
      _ = b.left ≫ T.hom := by rw [← Category.assoc, sq'.fac_right]
      _ = Y.hom := Over.w b)
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply Over.OverMorphism.ext
    exact sq'.fac_left
  · apply Over.OverMorphism.ext
    exact sq'.fac_right

/--
概要：基底上の全ての horn の持ち上げ性から忘却後の Kan 条件を得る。
方針：下の標準単体と終域の構造射の合成を基底として正方形をスライスへ移す。
規約：Segal 1974 Proposition 1.6 の補助。外側 horn も含む。
使われ方：写像空間の右随伴が Kan fibration となること。
-/
theorem underlying_rlp_of_over_horns {B : SSet.{u}} {OX OY : Over B} (p : OX ⟶ OY)
    (hp : ∀ (n : ℕ) (k : Fin (n + 2)) (b : (Δ[n + 1] : SSet.{u}) ⟶ B),
      HasLiftingProperty (hornOverMap k b) p) : SSet.modelCategoryQuillen.J.rlp p.left := by
  intro A D i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  constructor
  intro a b sq
  let base := b ≫ OY.hom
  let a' : Over.mk ((Λ[n + 1, k]).ι ≫ base) ⟶ OX := Over.homMk a (by
    calc
      a ≫ OX.hom = a ≫ (p.left ≫ OY.hom) := by rw [Over.w p]
      _ = (Λ[n + 1, k]).ι ≫ base := by rw [← Category.assoc, sq.w, Category.assoc])
  let b' : Over.mk base ⟶ OY := Over.homMk b
  let sq' : CommSq a' (hornOverMap k base) p b' := ⟨by
    apply Over.OverMorphism.ext
    exact sq.w⟩
  let := hp n k base
  exact ⟨⟨{
    l := sq'.lift.left
    fac_left := congrArg (fun f => f.left) sq'.fac_left
    fac_right := congrArg (fun f => f.left) sq'.fac_right }⟩⟩

end SerrePositivity.KST.Comparison

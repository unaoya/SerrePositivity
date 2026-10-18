module

public import SerrePositivity.KST.Comparison.OverHornLifting

/-!
# スライスの右随伴による trivial fibration の保存

概要：任意の基底変換と忘却の右随伴は、全単射的右持ち上げ性を保つ。
方針：引き戻しの単射保存と、随伴の持ち上げ性の対応を使う。
規約：Segal 1974 Lemma 1.7 の厳密化への補助。基底の Kan 性は不要。
使われ方：単射に沿う部分切断の対象による trivial fibration の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：スライス内の全ての単射の持ち上げ性から、忘却した射の全単射的右持ち上げ性を得る。
方針：底の写像と構造射の合成で問題をスライスへ移し、得た対角射を忘れる。
規約：単射性はスライスの射の基礎写像で指定する。
使われ方：右随伴の像の trivial fibration 性。
-/
theorem underlying_rlp_of_over_monos {B : SSet.{u}} {OX OY : Over B} (p : OX ⟶ OY)
    (hp : ∀ {X Y : Over B} (i : X ⟶ Y), Mono i.left → HasLiftingProperty i p) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp p.left := by
  intro A D i hi
  let : Mono i := hi
  constructor
  intro a b sq
  let base := b ≫ OY.hom
  let i' : Over.mk (i ≫ base) ⟶ Over.mk base := Over.homMk i
  let a' : Over.mk (i ≫ base) ⟶ OX := Over.homMk a (by
    calc
      a ≫ OX.hom = a ≫ (p.left ≫ OY.hom) := by rw [Over.w p]
      _ = i ≫ base := by rw [← Category.assoc, sq.w, Category.assoc])
  let b' : Over.mk base ⟶ OY := Over.homMk b
  let sq' : CommSq a' i' p b' := ⟨by
    apply Over.OverMorphism.ext
    exact sq.w⟩
  let := hp i' (inferInstanceAs (Mono i))
  exact ⟨⟨{
    l := sq'.lift.left
    fac_left := congrArg (fun f => f.left) sq'.fac_left
    fac_right := congrArg (fun f => f.left) sq'.fac_right }⟩⟩

/--
概要：任意の射に沿う積と忘却の右随伴は、全ての単射に対する右持ち上げ性を保つ。
方針：スライスの単射を引き戻しても単射であることと、随伴の持ち上げ性を使う。
規約：基底の射自身の Kan 性も不要。
使われ方：部分切断の対象を作る右随伴の像の trivial fibration 性。
-/
theorem sliceFiberRightAdjoint_allMono_rlp {E B K L : SSet.{u}} (p : E ⟶ B)
    (q : K ⟶ L) (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (((sliceFiberFunctor p).rightAdjoint.map q).left) := by
  let F := sliceFiberFunctor p
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  apply underlying_rlp_of_over_monos
  intro X Y i hi
  let : Mono i.left := hi
  have hmono : Mono (F.map i) := (sliceFiberFunctor_map_isPullback p i).mono_fst_of_mono
  exact (adj.hasLiftingProperty_iff i q).mp (hq _ hmono)

end SerrePositivity.KST.Comparison

import Mathlib.Data.Finset.Card

/-!
  A finite, two-colour version of the blue-eyes puzzle.
  `World N` is the set of blue-eyed residents; all others are brown-eyed.
  A resident's only alternative to the actual world changes their own colour.
-/

namespace BlueEyes

abbrev World (N : ℕ) := Finset (Fin N)

def flip {N : ℕ} (w : World N) (i : Fin N) : World N :=
  if i ∈ w then w.erase i else insert i w

def blueCount {N : ℕ} (w : World N) : ℕ := w.card

-- `X` is the set of worlds consistent with all public information so far.
def knows {N : ℕ} (X : World N → Prop) (w : World N) (i : Fin N) : Prop :=
  ¬ X (flip w i)

-- The answer vector is public, truthful, and simultaneous.
def update {N : ℕ} (X : World N → Prop) (w : World N) : World N → Prop :=
  fun v => X v ∧ ∀ i, knows X v i ↔ knows X w i

def unrestricted {N : ℕ} : World N → Prop := fun _ => True
def atLeast {N : ℕ} (k : ℕ) : World N → Prop := fun w => k ≤ blueCount w

theorem flip_mem_self {N : ℕ} (w : World N) (i : Fin N) :
    (i ∈ flip w i) ↔ i ∉ w := by
  unfold flip
  split_ifs with h
  · simp [h]
  · simp [h]

theorem flip_card_blue {N : ℕ} (w : World N) (i : Fin N) (h : i ∈ w) :
    blueCount (flip w i) + 1 = blueCount w := by
  have hp : 0 < w.card := Finset.card_pos.mpr ⟨i, h⟩
  simp [blueCount, flip, h, Finset.card_erase_of_mem h]
  omega

theorem flip_card_brown {N : ℕ} (w : World N) (i : Fin N) (h : i ∉ w) :
    blueCount (flip w i) = blueCount w + 1 := by
  simp [blueCount, flip, h, Finset.card_insert_of_notMem h]

theorem no_outsider_never_knows {N : ℕ} (w : World N) (i : Fin N) :
    ¬ knows (unrestricted (N := N)) w i := by
  simp [knows, unrestricted]

theorem no_outsider_update {N : ℕ} (w : World N) :
    update (unrestricted (N := N)) w = unrestricted := by
  funext v
  simp [update, knows, unrestricted]

-- After k-1 all-unknown days, the remaining worlds have at least k blue eyes.
theorem blue_knows_at_threshold {N k : ℕ} (w : World N) (i : Fin N)
    (hi : i ∈ w) (hw : k ≤ blueCount w) :
    knows (atLeast k) w i ↔ blueCount w = k := by
  unfold knows atLeast
  have hc := flip_card_blue w i hi
  omega

theorem brown_does_not_know_at_threshold {N k : ℕ} (w : World N) (i : Fin N)
    (hi : i ∉ w) (hw : k ≤ blueCount w) :
    ¬ knows (atLeast k) w i := by
  unfold knows atLeast
  have hc := flip_card_brown w i hi
  omega

theorem all_unknown_above_threshold {N k : ℕ} (w : World N)
    (hw : k + 1 ≤ blueCount w) :
    ∀ i, ¬ knows (atLeast k) w i := by
  intro i
  by_cases hi : i ∈ w
  · rw [blue_knows_at_threshold w i hi (by omega)]
    omega
  · exact brown_does_not_know_at_threshold w i hi (by omega)

theorem all_unknown_iff {N k : ℕ} (w : World N) (hk : 1 ≤ k)
    (hw : k ≤ blueCount w) :
    (∀ i, ¬ knows (atLeast k) w i) ↔ k + 1 ≤ blueCount w := by
  constructor
  · intro h
    by_contra hn
    have heq : blueCount w = k := by omega
    have hpos : 0 < w.card := by simp only [blueCount] at heq; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact h i ((blue_knows_at_threshold w i hi hw).2 heq)
  · exact all_unknown_above_threshold w

theorem update_after_all_unknown {N k : ℕ} (w : World N)
    (hk : 1 ≤ k) (hw : k + 1 ≤ blueCount w) :
    update (atLeast k) w = atLeast (k + 1) := by
  funext v
  apply propext
  have hreal := all_unknown_above_threshold w hw
  constructor
  · rintro ⟨hv, hvec⟩
    apply (all_unknown_iff v hk hv).mp
    intro i hknow
    exact hreal i ((hvec i).mp hknow)
  · intro hv
    refine ⟨(by unfold atLeast at *; omega), ?_⟩
    intro i
    have hother := all_unknown_above_threshold v hv i
    exact iff_of_false hother (hreal i)

theorem declarations_on_blue_day {N n : ℕ} (w : World N)
    (hw : blueCount w = n) (i : Fin N) :
    knows (atLeast n) w i ↔ i ∈ w := by
  by_cases hi : i ∈ w
  · simp [hi, (blue_knows_at_threshold w i hi (by omega)).2 hw]
  · have h := brown_does_not_know_at_threshold (k := n) w i hi (by omega)
    simp [hi, h]

theorem brown_knows_after_blue_day {N n : ℕ} (w : World N)
    (hn : 1 ≤ n) (hw : blueCount w = n) (i : Fin N) (hi : i ∉ w) :
    knows (update (atLeast n) w) w i := by
  unfold knows
  intro hflip
  have hpos : 0 < w.card := by simp only [blueCount] at hw; omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hvec := hflip.2 j
  have hcount : blueCount (flip w i) = n + 1 := by
    rw [flip_card_brown w i hi, hw]
  have hunk := all_unknown_above_threshold (flip w i)
    (by omega : n + 1 ≤ blueCount (flip w i)) j
  exact hunk (hvec.mpr ((declarations_on_blue_day w hw j).2 hj))

def noOutsiderState {N : ℕ} (w : World N) : ℕ → World N → Prop
  | 0 => unrestricted
  | t + 1 => update (noOutsiderState w t) w

theorem no_outsider_all_days {N : ℕ} (w : World N) (t : ℕ) :
    noOutsiderState w t = unrestricted := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [noOutsiderState, ih, no_outsider_update]

def outsiderState {N : ℕ} (w : World N) : ℕ → World N → Prop
  | 0 => atLeast 1
  | t + 1 => update (outsiderState w t) w

theorem outsider_silent_days {N : ℕ} (w : World N) (t : ℕ)
    (ht : t + 1 ≤ blueCount w) :
    outsiderState w t = atLeast (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprev : t + 1 ≤ blueCount w := by omega
      rw [outsiderState, ih hprev]
      exact update_after_all_unknown w (by omega) (by omega)

theorem blue_day {N n : ℕ} (w : World N) (hn : 1 ≤ n)
    (hw : blueCount w = n) (i : Fin N) :
    knows (outsiderState w (n - 1)) w i ↔ i ∈ w := by
  have hstate : outsiderState w (n - 1) = atLeast n := by
    have h := outsider_silent_days w (n - 1) (by rw [hw]; omega)
    have hidx : n - 1 + 1 = n := by omega
    simpa only [hidx] using h
  rw [hstate]
  exact declarations_on_blue_day w hw i

theorem brown_next_day {N n : ℕ} (w : World N) (hn : 1 ≤ n)
    (hw : blueCount w = n) (i : Fin N) (hi : i ∉ w) :
    knows (outsiderState w n) w i := by
  have hstate : outsiderState w (n - 1) = atLeast n := by
    have h := outsider_silent_days w (n - 1) (by rw [hw]; omega)
    have hidx : n - 1 + 1 = n := by omega
    simpa only [hidx] using h
  have hsucc : n - 1 + 1 = n := by omega
  rw [← hsucc, outsiderState, hstate]
  exact brown_knows_after_blue_day w hn hw i hi

theorem everyone_next_day {N n : ℕ} (w : World N) (hn : 1 ≤ n)
    (hw : blueCount w = n) (i : Fin N) :
    knows (outsiderState w n) w i := by
  by_cases hi : i ∈ w
  · have hstate : outsiderState w (n - 1) = atLeast n := by
      have h := outsider_silent_days w (n - 1) (by rw [hw]; omega)
      have hidx : n - 1 + 1 = n := by omega
      simpa only [hidx] using h
    have hsucc : n - 1 + 1 = n := by omega
    rw [← hsucc, outsiderState, hstate]
    unfold knows update
    intro hflip
    have hcount := flip_card_blue w i hi
    have hsmall : ¬ n ≤ blueCount (flip w i) := by omega
    exact hsmall hflip.1
  · exact brown_next_day w hn hw i hi

end BlueEyes

"""Exercise the actual polling loop without taking a shared build lock."""
from pathlib import Path
import unittest


class BoundaryClock:
    def __init__(self, ticks):
        self.ticks = iter(ticks)
        self.delays = []

    def monotonic(self):
        return next(self.ticks)

    def sleep(self, delay):
        if delay < 0:
            raise ValueError("sleep length must be non-negative")
        self.delays.append(delay)


class LockPollingTests(unittest.TestCase):
    def run_poll(self, ticks, interrupted=False):
        source = Path(__file__).with_name("with_build_lock.sh").read_text()
        loops = [line.strip() for line in source.splitlines()
                 if line.strip().startswith("while time.monotonic()<until and not interrupted:")]
        self.assertEqual(len(loops), 1)
        clock = BoundaryClock(ticks)
        exec(loops[0], {"time": clock, "until": 1.0, "interrupted": interrupted})
        return clock.delays

    def test_deadline_crossed_between_condition_and_sleep(self):
        self.assertEqual(self.run_poll([0.99, 1.01, 1.02]), [0.0])

    def test_normal_slice(self):
        delays = self.run_poll([0.90, 0.95, 1.01])
        self.assertEqual(len(delays), 1)
        self.assertAlmostEqual(delays[0], 0.05)

    def test_already_expired(self):
        self.assertEqual(self.run_poll([1.0]), [])

    def test_interrupted(self):
        self.assertEqual(self.run_poll([0.9], interrupted=True), [])


if __name__ == "__main__":
    unittest.main()

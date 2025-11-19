/**
 * Vitest setup file
 *
 * This file runs before all tests and sets up the test environment.
 */

import { beforeAll, afterAll, afterEach } from 'vitest';

// Setup before all tests
beforeAll(() => {
  // Set timezone to UTC for consistent date/time testing
  process.env.TZ = 'UTC';

  // Disable colors in test output for snapshot consistency
  process.env.NO_COLOR = '1';

  // Set NODE_ENV to test
  process.env.NODE_ENV = 'test';
});

// Cleanup after each test
afterEach(() => {
  // Clear mocks
  // jest.clearAllMocks(); // If using jest compatibility
});

// Cleanup after all tests
afterAll(() => {
  // Cleanup resources if needed
});

// Extend matchers or add global test utilities here
// Example: Add custom matchers for validation results
declare module 'vitest' {
  interface Assertion {
    toBeValidResult(): void;
    toHaveError(code: string): void;
  }
}

// Custom matchers (optional)
// expect.extend({
//   toBeValidResult(received) {
//     const pass = received.valid === true;
//     return {
//       pass,
//       message: () =>
//         pass
//           ? 'Expected result to be invalid'
//           : 'Expected result to be valid',
//     };
//   },
// });
